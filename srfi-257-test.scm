(import (scheme base) (srfi 64))
(import (srfi 257) (srfi 257 misc) (srfi 111) (srfi 257 box))

; SRFI 257 Tests (borrowed from many sources)

(test-begin "srfi-257")

(define-syntax test-matcher 
  (syntax-rules ()
    ((_ matcher (in out) ...)
     (let ((m matcher))
       (test-equal 'out (matcher 'in)) ...))))

(define-syntax test-restart 
  (syntax-rules ()
    ((_ matcher-k in . outs)
     (let ((mk matcher-k) (v '()))
      (mk 'in (lambda (x) (set! v (cons x v))))
      (test-equal (reverse v) 'outs)))))


; simple matches
(define (matcher-1 x)
  (match x
    (1                                'number-one)
    ('a                               'symbol-a)
    ('(a b)                           'list-a-b)
    (`(,v q)                          `(list ,v q))
    (`((,x ,y) (,z ,x))               `(head&tail ,x ,y ,z))
    (`(+ 0 ,a ,a)                     `(* 2 ,a))
    (`(+ (,f ,@a) (,g ,@a))           `((+ ,f ,g) ,@a))
    (`(** ,(~number? a) ,(~number? b)) (expt a b))
    (w                                `(generic ,w))))

(test-matcher matcher-1
  (1                          number-one)
  (a                          symbol-a)
  (((x y) q)                  (list (x y) q))
  (((a 2) (b a))              (head&tail a 2 b))
  ((+ 0 (+ y z) (+ y z))      (* 2 (+ y z)))
  ((+ (sin a b) (cos a b))    ((+ sin cos) a b))
  ((** 2 4)                   16)
  ((** 2 a)                   (generic (** 2 a))))

; rollback to the next rule
(define (matcher-2 x k)
  (match x
    (`(,@a ,(~symbol? b) ,@c) (=> next) (k `(p1 ,a ,b ,c)) (next))
    (`(,@a ,@c ,x)            (=> next) (k `(p2 ,a ,c ,x)) (next))
    (x                       (k `(p3 ,x)))))

(test-restart matcher-2
  (1 2 3 a 4 5)
  (p1 (1 2 3) a (4 5))
  (p2 (1 2 3 a 4) () 5)
  (p3 (1 2 3 a 4 5)))

; rollback to the next match
(define (matcher-3 x k)
  (match x
    (`(,@a ,b ,@c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (`(,@a ,@c)    (=> next back) (k `(snd ,a ,c)) (back))
    (`,x               (k `(final ,x)))))

(test-restart matcher-3
  (1 2 3 4 5)
  (fst (1 2 3 4) 5 ())
  (fst (1 2 3) 4 (5))
  (fst (1 2) 3 (4 5))
  (fst (1) 2 (3 4 5))
  (fst () 1 (2 3 4 5))
  (snd (1 2 3 4 5) ())
  (snd (1 2 3 4) (5))
  (snd (1 2 3) (4 5))
  (snd (1 2) (3 4 5))
  (snd (1) (2 3 4 5))
  (snd () (1 2 3 4 5))
  (final (1 2 3 4 5)))

; rollback to the next match, constructor syntax
(define (matcher-4 x k)
  (match x
    ((~append a (~list b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~append a c)           (=> next back) (k `(snd ,a ,c)) (back))
    (x                       (k `(final ,x)))))

(test-restart matcher-4
  (1 2 3 4 5)
  (fst (1 2 3 4) 5 ())
  (fst (1 2 3) 4 (5))
  (fst (1 2) 3 (4 5))
  (fst (1) 2 (3 4 5))
  (fst () 1 (2 3 4 5))
  (snd (1 2 3 4 5) ())
  (snd (1 2 3 4) (5))
  (snd (1 2 3) (4 5))
  (snd (1 2) (3 4 5))
  (snd (1) (2 3 4 5))
  (snd () (1 2 3 4 5))
  (final (1 2 3 4 5)))

; same, but with strings
(define (matcher-5 x k)
  (match x
    ((~string-append a (~string b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~string-append a c)             (=> next back) (k `(snd ,a ,c)) (back))
    (x                                (k `(final ,x)))))

(test-restart matcher-5
  "12345"
  (fst "1234" #\5 "")
  (fst "123" #\4 "5")
  (fst "12" #\3 "45")
  (fst "1" #\2 "345")
  (fst "" #\1 "2345")
  (snd "12345" "")
  (snd "1234" "5")
  (snd "123" "45")
  (snd "12" "345")
  (snd "1" "2345")
  (snd "" "12345")
  (final "12345"))

(define (matcher-5ng x k)
  (match x
    ((~string-append/ng a (~string b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~string-append/ng a c)             (=> next back) (k `(snd ,a ,c)) (back))
    (x                                           (k `(final ,x)))))

(test-restart matcher-5ng
  "12345"
  (fst "" #\1 "2345")
  (fst "1" #\2 "345")
  (fst "12" #\3 "45")
  (fst "123" #\4 "5")
  (fst "1234" #\5 "")
  (snd "" "12345")
  (snd "1" "2345")
  (snd "12" "345")
  (snd "123" "45")
  (snd "1234" "5")
  (snd "12345" "")
  (final "12345"))

; nonlinear matcher - 6
(define (string-reverse s) (list->string (reverse (string->list s))))
(define (matcher-6 x k)
  (match x
    ((~string-append a b a) (=> next back) (k `(rep ,a ,b ,a)) (back))
    ((~string-append a b (~= string-reverse a)) (=> next back) (k `(rev ,a ,b ,(string-reverse a))) (back))
    (x (k `(final ,x)))))

(test-restart matcher-6
  "abracadarba"
  (rep "a" "bracadarb" "a")
  (rep "" "abracadarba" "")
  (rev "abra" "cad" "arba")
  (rev "abr" "acada" "rba")
  (rev "ab" "racadar" "ba")
  (rev "a" "bracadarb" "a")
  (rev "" "abracadarba" "")
  (final "abracadarba"))

; advanced non-iterative matches

(define-match-pattern ~list4? ()
  ((_) (~and (~list?) (~= length 4)))
  ((_ l) (~and (~list?) (~= length 4) l)))

(define-match-pattern ~listn? ()
  ((_ n) (~and (~list?) (~= length n)))
  ((_ n l) (~and (~list?) (~= length n) l)))

(define (matcher-7 x)
  (match x
    ((~or 1 2 3)                      'number-1-3)
    ((~or 'a 'b 'c)                   'symbol-a-c)
    ((~? symbol?)                     'symbol-other)
    ((~and l `(a ,b))                 `(list-a-* ,l ,b))
    ((~char? c)                       'char)
    ((~and (~list?) (~= length 3) l)  `(list-of-3 ,l))
    ((~list4? l)                      `(list-of-4 ,l))
    ((~listn? 5 l)                    `(list-of-5 ,l))
    ((~and (~list? l) (~not (~= length 3)))  `(list-of-not-3 ,l))
    (w                                `(other ,w))))

(test-matcher matcher-7
  (1                          number-1-3)
  (2                          number-1-3)
  (4                          (other 4))
  (a                          symbol-a-c)
  (z                          symbol-other)
  (#\z                        char)
  ((a 1)                      (list-a-* (a 1) 1))
  ((1 2 3)                    (list-of-3 (1 2 3)))
  ((1 2 3 4)                  (list-of-4 (1 2 3 4)))
  ((1 2 3 4 5)                (list-of-5 (1 2 3 4 5)))
  ((1 2 3 4 5 6)              (list-of-not-3 (1 2 3 4 5 6))))

; tests for ~list-no-order / ~list-no-order*

(define (matcher-lno x k)
  (match x
    ((~list-no-order a b c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-lno
  (1 2 3)
  (fst 1 2 3)
  (fst 1 3 2)
  (fst 2 1 3)
  (fst 2 3 1)
  (fst 3 2 1)
  (fst 3 1 2)
  (final (1 2 3)))

(define (matcher-lno* x k)
  (match x
    ((~list-no-order* a b (~etc (~list c))) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-lno*
  ((1) (2) (3) (4))
  (fst (1) (2) (3 4))
  (fst (1) (3) (2 4))
  (fst (1) (4) (3 2))
  (fst (2) (1) (3 4))
  (fst (2) (3) (1 4))
  (fst (2) (4) (3 1))
  (fst (3) (2) (1 4))
  (fst (3) (1) (2 4))
  (fst (3) (4) (1 2))
  (fst (4) (3) (2 1))
  (fst (4) (2) (3 1))
  (fst (4) (1) (2 3))
  (final ((1) (2) (3) (4))))

; tests for ~or

(define-match-pattern ~opt ()
  ((_ p) (~or (~list p) '())))

(define (matcher-or x)
  (match x
    ((~or 1 2 3)                                'number-1-3)
    ((~or 'a 'b 'c)                             'symbol-a-c)
    ((~or `(,@a ,(~symbol? b) ,@a) '())         `(mp3 ,a ,b ,a))
    (`(foo ,n ,@(~opt `(align ,a)) ,x)          `(foo ,n ,a ,x))
    ((~or x y z)                                `(xyz ,x ,y ,z))))

(test-matcher matcher-or
  (1                          number-1-3)
  (2                          number-1-3)
  (4                          (xyz 4 #f #f))
  (a                          symbol-a-c)
  (z                          (xyz z #f #f))
  (()                         (mp3 #f #f #f))
  ((a)                        (mp3 () a ()))
  ((a b)                      (xyz (a b) #f #f))
  ((a b c)                    (xyz (a b c) #f #f))
  ((a b . c)                  (xyz (a b . c) #f #f))
  ((y z x y z)                (mp3 (y z) x (y z)))
  ((foo bar baz)              (foo bar #f baz))
  ((foo bar (align 16) baz)   (foo bar 16 baz)))

(define (matcher-or2 x k)
  (match x
    (`(,@a ,(~and b (~or 'b 'c)) ,@c)          (=> next back) (k `(p1 ,a ,b ,c)) (back))
    (`(,@a ,@(~and b (~or '() '(d))) ,@c)      (=> next back) (k `(p2 ,a ,b ,c)) (back))
    (x                                         (k `(p3 ,x)))))

(test-restart matcher-or2
  (1 a 2 b 3 c 4 d 5)
  (p1 (1 a 2 b 3) c (4 d 5))
  (p1 (1 a 2) b (3 c 4 d 5))
  (p2 (1 a 2 b 3 c 4 d 5) () ())
  (p2 (1 a 2 b 3 c 4 d) () (5))
  (p2 (1 a 2 b 3 c 4) (d) (5))
  (p2 (1 a 2 b 3 c 4) () (d 5))
  (p2 (1 a 2 b 3 c) () (4 d 5))
  (p2 (1 a 2 b 3) () (c 4 d 5))
  (p2 (1 a 2 b) () (3 c 4 d 5))
  (p2 (1 a 2) () (b 3 c 4 d 5))
  (p2 (1 a) () (2 b 3 c 4 d 5))
  (p2 (1) () (a 2 b 3 c 4 d 5))
  (p2 () () (1 a 2 b 3 c 4 d 5))
    (p3 (1 a 2 b 3 c 4 d 5)))

; tests for ~etc and etc

(define (matcher-etc x)
  (match x
    ((~append (~etc (~cons x y)) (~pair? (~etc (~number? z))))          `(first ,x ,y ,z))
    ((~append (~etc (~cons x (~append (~etc y) '()))) '())              `(second ,x ,y))
    ((~cons (~etc (~symbol? x)) (~etc (~cons x y)))                     `(third ,x ,y))
    ((~cons (~and x (~etc (~number?))) (~append (~etc (~cons x y)) z))  `(fourth ,x ,y ,z))
    ((~append (~pair? (~etc (~pair? x))) (~cons y _))                   `(fifth ,x ,y))
    (_                                                                  `(other))))

(test-matcher matcher-etc
  (((1) (2) (3 . 4) 5 6)                      (first (1 2 3) (() () 4) (5 6)))
  (((a b c d) (e f g) (h i) (j))              (second (a e h j) ((b c d) (f g) (i) ())))
  (((a b c) (a . 2) (b . 3) (c . 4))          (third (a b c) (2 3 4)))
  (((2 3) (2) (3 . 4) (5 . 6))                (fourth (2 3) (() 4) ((5 . 6))))
  (((2 3) (1 . 2) (1 . 3) (1 . 4))            (fifth ((2 3) (1 . 2) (1 . 3)) (1 . 4)))
  ((1 (1 . 2) (1 . 3) (2 . 6))                (other)))

(define *foobar* 42)

(define (matcher-etcetc x)
  (match x
    ((~etc (~list* 1 x y))     (cons 'first (etc (list (value *foobar*) y x))))
    ((~etc (~etc (~list x y))) (cons 'second (etc (etc (list y x)))))
    ((~etc (~cons x y))        (cons 'third (list (etc (cons x x)) (etc (cons y 4)))))
    (_                         (value '(other)))))

(test-matcher matcher-etcetc
  (((1 1) (1 2) (1 3 4))                      (first (42 () 1) (42 () 2) (42 (4) 3)))
  ((((a b) (c d)) ((e f) (g h) (i j)) ())     (second ((b a) (d c)) ((f e) (h g) (j i)) ()))
  (((a b c) (a . 2) (b . 3) (c . 4))          (third ((a . a) (a . a) (b . b) (c . c)) (((b c) . 4) (2 . 4) (3 . 4) (4 . 4))))
  ((1 (1 . 2) (1 . 3) (2 . 6))                (other)))


; custom matcher with (extended) lambda-list-like patterns

(define-match-pattern ~llp->p (quote quasiquote)
  ((_ 'x) 'x)
  ((_ `x) `x)
  ((_ ()) '())
  ((_ (x . y)) (~cons (~llp->p x) (~llp->p y)))
  ((_ #(x ...)) (~vector (~llp->p x) ...))
  ;((_ #&x) (~box (~llp->p x)))
  ((_ other) other)) ; covers strings, numbers, chars, bytevectors, vars, and _

(define-syntax ll-match
  (syntax-rules ()
    ((_ x (llp . rhs) ...)
     (match x ((~llp->p llp) . rhs) ...))))

(define (matcher-8 x)
  (ll-match x
    (1                        'number-one)
    ('a                       'symbol-a)
    ((_)                      'list1)
    ('(a b)                   'list-a-b)
    (()                       'null)
    ((x 'q)                   `(list ,x q))
    ((x 42 . z)               `(list2+/42 ,x 42 ,z))
    ((x y . z)                `(list2+ ,x ,y ,z))
    (#('point x y)            `(point2 ,x ,y))
    (#('point x y 0)          `(point2 ,x ,y))
    (#('point x y z)          `(point3 ,x ,y ,z))
    (z                        `(other ,z))))

(test-matcher matcher-8
  (1                         number-one)
  (a                         symbol-a)
  (()                        null)
  ((a)                       list1)
  ((a b)                     list-a-b)
  ((p q)                     (list p q))
  ((41 42 43 44)             (list2+/42 41 42 (43 44)))
  ((45 46 47 48)             (list2+ 45 46 (47 48)))
  (#(point 49 50)            (point2 49 50))
  (#(point 49 50 0)          (point2 49 50))
  (#(point 49 50 51)         (point3 49 50 51))
  (#(point 52 53 54 55)      (other #(point 52 53 54 55))))


; avp's m5-compatible matcher tests

(define-match-pattern ~m5p->p (quote unquote unquote-splicing and)
  ((_ 'x) 'x)
  ((_ ,(x)) x)
  ((_ ,(x p?)) (~? p? x))
  ((_ ,(x p? . p?*)) (~? p? (~m5p->p ,(x . p?*))))
  ((_ ,x) x)
  ((_ ()) '())
  ((_ (and p ...)) (~and (~m5p->p p) ...))
  ((_ (,@x . y)) (~append/ng x (~m5p->p y)))
  ((_ (x . y)) (~cons (~m5p->p x) (~m5p->p y)))
  ((_ #(x ...)) (~list->vector (~m5p->p (x ...))))
  ;((_ #&x) (~box (~m5p->p x)))
  ((_ other) 'other))

(define-syntax m5-match
  (syntax-rules (=> ==>)
    ((_ () x () (c ...))
     (match x c ...))
    ((_ () x ((m5p => e) m5c ...) (c ...))
     (m5-match () x (m5c ...) (c ... ((~m5p->p m5p) (=> n) (e n)))))
    ((_ () x ((m5p ==> e) m5c ...) (c ...))
     (m5-match () x (m5c ...) (c ... ((~m5p->p m5p) (=> n b) (e b n)))))
    ((_ () x ((m5p e ...) m5c ...) (c ...))
     (m5-match () x (m5c ...) (c ... ((~m5p->p m5p) (begin e ...)))))
    ((_ x m5c ...)
     (m5-match () x (m5c ...) ()))))

; original m5 matcher tests (avp)

(define (m5-matcher-1 x)
  (m5-match x
    (1                              'number-one)
    (a                              'symbol-a)
    ((a b)                          'list-a-b)
    ((,v q)                         `(list ,v q))
    (((,x ,y) (,z ,x))              `(head&tail ,x ,y ,z))
    ((+ 0 ,a ,a)                    `(* 2 ,a))
    ((+ (,f ,@a) (,g ,@a))          `((+ ,f ,g) ,@a))
    ((** ,(a number?) ,(b number?)) (expt a b))
    ((and ,x (,y ,z))               `(deconstructed ,x ,y ,z))
    (,w                             `(generic ,w))))

(test-matcher m5-matcher-1
  (1                          number-one)
  (a                          symbol-a)
  (((x y) q)                  (list (x y) q))
  (((a 2) (b a))              (head&tail a 2 b))
  ((+ 0 (+ y z) (+ y z))      (* 2 (+ y z)))
  ((+ (sin a b) (cos a b))    ((+ sin cos) a b))
  ((** 2 4)                   16)
  ((** 2 a)                   (generic (** 2 a)))
  ((123 456)                  (deconstructed (123 456) 123 456)))

; m5's substitute for limited or pattern
(define (in? . lst) (lambda (x) (member x lst)))

(define (m5-matcher-or x)
  (m5-match x
    ((,a ,(b (in? 2 3 5 7 11 13)))             'first)
    ((,(a number?) ,(b (in? 4 9 (* a a a))))   'squared)
    ((,a ,a)                                   'second)
    ((,a ,b)                                   'third)
    ((',a)                                     'quoted)
    (,v                                        'fourth)))

(test-matcher m5-matcher-or
  (1                   fourth)
  ((x x)               second)
  ((5 125)             squared)
  ((1 4)               squared)
  ((5 14)              third)
  ((,a)                quoted)
  ((,ab)               fourth)
  ((foo 13)            first))

(define (m5-matcher-2 x k)
  (m5-match x
    ((,@a ,(b symbol?) ,@c)  => (lambda (next) (k `(p1 ,a ,b ,c)) (next)))
    ((,@a ,@c ,x)            => (lambda (next) (k `(p2 ,a ,c ,x)) (next)))
    (,x                      (k `(p3 ,x)))))

(test-restart m5-matcher-2
  (1 2 3 a 4 5)
  (p1 (1 2 3) a (4 5))
  (p2 () (1 2 3 a 4) 5)
  (p3 (1 2 3 a 4 5)))

;; rollback to the next match

(define (m5-matcher-3 x k)
  (m5-match x
    ((,@a ,(b symbol?) ,@c) ==> (lambda (next nr) (k `(fst ,a ,b ,c)) (next)))
    ((,@a ,@c)              ==> (lambda (next nr) (k `(snd ,a ,c)) (next)))
    (,x                     (k `(final ,x)))))

(test-restart m5-matcher-3
  (1 x 3 y 5)
  (fst (1) x (3 y 5))
  (fst (1 x 3) y (5))
  (snd () (1 x 3 y 5))
  (snd (1) (x 3 y 5))
  (snd (1 x) (3 y 5))
  (snd (1 x 3) (y 5))
  (snd (1 x 3 y) (5))
  (snd (1 x 3 y 5) ())
  (final (1 x 3 y 5)))


; tests of syntax-rules -like matcher with standalone list of literal symbols

(test-matcher
  (lambda (in)
    (sr-match in (a b)
      ((a x) 1)
      ((b x y) 2)
      ((a x y) 3)
      ((_ _ _) 4)))
  ((a 17 37) 3)
  ((b 17 37) 2)
  ((c 17 37) 4))

(test-matcher
  (lambda (in)
    (sr-match in (a)
      ((a x* ...) x*)))
  ((a 17 37) (17 37)))

(test-matcher
  (lambda (in)
    (sr-match in (begin)
      ((begin (x* y*) ...) (list x* y*))))
  ((begin (1 5) (2 6) (3 7) (4 8)) ((1 2 3 4) (5 6 7 8))))

(test-matcher
  (lambda (in)
    (sr-match in ()
      (((x* y** ...) ...) (list x* y**))))
  (((a b c d) (e f g) (h i) (j)) ((a e h j) ((b c d) (f g) (i) ()))))


; tests of SRFI-241/DFH-like catamorphism matcher

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x) 1)
      ((b ,x ,y) 2)
      ((a ,x ,y) 3)
      ((,_ ,_ ,_) 4)))
  ((a 17 37) 3)
  ((b 17 37) 2)
  ((c 17 37) 4))

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x) (- x))
      ((b ,x ,y) (+ x y))
      ((a ,x ,y) (* x y))))
  ((a 17 37) 629))

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x* ...) x*)))
  ((a 17 37) (17 37)))

(test-matcher
  (lambda (in)
    (cm-match in
      ((begin (,x* ,y*) ...) (append x* y*))))
  ((begin (1 5) (2 6) (3 7) (4 8)) (1 2 3 4 5 6 7 8)))

(test-matcher
  (lambda (in)
    (cm-match in
      (((,x* ,y** ...) ...) (list x* y**))))
  (((a b c d) (e f g) (h i) (j)) ((a e h j) ((b c d) (f g) (i) ()))))

(test-matcher
  (lambda (in)
    (letrec
      ((len (lambda (lst)
              (cm-match lst
                (() 0)
                ((,x ,x* ...) (+ 1 (len x*)))))))
      (len in)))
  ((a b c d) 4))

(test-matcher
  (lambda (in)
    (let ((len
           (lambda (lst)
             (cm-match lst
               (() 0)
               ((,x . ,(y)) (+ 1 y))))))
      (len in)))
  ((a b c d) 4))

(test-matcher
  (lambda (in)
    (let ((split
           (lambda (lis)
             (cm-match lis
               (() (values '() '()))
               ((,x) (values `(,x) '()))
               ((,x ,y . ,(odds evens))
                (values `(,x . ,odds)
                        `(,y . ,evens)))))))
      (call-with-values (lambda () (split in)) vector)))
  ((a b c d e f) #((a c e) (b d f))))

(test-matcher
  (lambda (in)
    ; NB: SRFI-241 erroneously uses 'let' in this example
    (letrec ((split
              (lambda (lis)
                (cm-match lis
                  (() (values '() '()))
                  ((,x) (values `(,x) '()))
                  ((,x ,y . ,(split -> odds evens))
                    (values `(,x . ,odds)
                            `(,y . ,evens)))))))
          (call-with-values (lambda () (split in)) vector)))
  ((a b c d e f) #((a c e) (b d f))))

(test-matcher
  (lambda (in)
    (let ((simple-eval
           (lambda (x)
             (cm-match x
               (,i (guard (integer? i)) i)
               ((+ ,(x*) ...) (apply + x*))
               ((* ,(x*) ...) (apply * x*))
               ((- ,(x) ,(y)) (- x y))
               ((/ ,(x) ,(y)) (/ x y))
               (,x (error "invalid expression" x))))))
      (simple-eval in)))
  ((+ (- 0 1) (+ 2 3)) 4)
  ((+ 1 2 3) 6))

(test-matcher
  (lambda (in)
    (let ((simple-eval
           (lambda (x)
             (cm-match x
               (,i (guard (integer? i)) i)
               ((+ ,(x*) ...) (apply + x*))
               ((* ,(x*) ...) (apply * x*))
               ((- ,(x) ,(y)) (- x y))
               ((/ ,(x) ,(y)) (/ x y))
               (,x (error "invalid expression" x))))))
      (simple-eval in)))
  ((+ (- 0 1) (+ 2 3)) 4))

; ellipsis-aware rhs quasiquote is not supported by cm-match,
; so the rhs qq SRFI-241 tests/examples are modified to use
; standard rhs quasiquote

(test-matcher
  (lambda (x)
    (define Prog
      (lambda (x)
        (cm-match x
          ((program ,(Stmt -> s*) ... ,(Expr -> e))
           `(begin ,@s* ,e))
          (,x (error "invalid program" x)))))
    (define Stmt
      (lambda (x)
        (cm-match x
          ((if ,(Expr -> e) ,(Stmt -> s1) ,(Stmt -> s2))
           `(if ,e ,s1 ,s2))
          ((set! ,v ,(Expr -> e))
           (guard (symbol? v))
           `(set! ,v ,e))
          (,x (error "invalid statement" x)))))
    (define Expr
      (lambda (x)
        (cm-match x
          (,v (guard (symbol? v)) v)
          (,n (guard (integer? n)) n)
          ((if ,(e1) ,(e2) ,(e3))
           `(if ,e1 ,e2 ,e3))
          ((,(rator) ,(rand*) ...) `(,rator ,@rand*))
          (,x (error "invalid expression" x)))))
    (Prog x))
  ((program (set! x 3) (+ x 4)) (begin (set! x 3) (+ x 4))))

(test-matcher
  (lambda (x)
    (define Prog
      (lambda (x)
        (cm-match x
          ((program ,(Stmt -> s*) ... ,((Expr '()) -> e))
           `(begin ,@s* ,e))
          (,x (error "invalid program" x)))))
    (define Stmt
      (lambda (x)
        (cm-match x
          ((if ,((Expr '()) -> e) ,(Stmt -> s1) ,(Stmt -> s2))
           `(if ,e ,s1 ,s2))
          ((set! ,v ,((Expr '()) -> e))
           (guard (symbol? v))
           `(set! ,v ,e))
          (,x (error "invalid statement" x)))))
    (define Expr
      (lambda (env)
        (lambda (x)
          (cm-match x
            (,v (guard (symbol? v)) v)
            (,n (guard (integer? n)) n)
            ((if ,(e1) ,(e2) ,(e3))
             (guard (not (memq 'if env)))
             `(if ,e1 ,e2 ,e3))
            ((let ((,v ,(e))) ,((Expr (cons v env)) -> body))
             (guard (not (memq 'let env)) (symbol? v))
             `(let ((,v ,e)) ,body))
            ((,(rator) ,(rand*) ...)
             `(call ,rator ,@rand*))
            (,x (error "invalid expression" x))))))
    (Prog x))
  ((program (let ((if (if x list values))) (if 1 2 3)))
   (begin (let ((if (if x list values))) (call if 1 2 3)))))

; box patterns tests

(test-equal #f (match '42 ((~box? a) a) (_ #f)))
(test-equal (box 42) (match (box 42) ((~box? a) a) (_ #f)))

(test-equal #f (match '42 ((~box a) a) (_ #f)))
(test-equal 42 (match (box 42) ((~box a) a) (_ #f)))

(test-end)
