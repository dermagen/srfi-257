;;; SPDX-FileCopyrightText: 2024 Sergei Egorov
;;; SPDX-License-Identifier: MIT

;========================================================================================
;
;  Simple extendable pattern matcher with backtracking       (c) 2024 Sergei Egorov
;
;========================================================================================

; Note: this file is made for loading intro a REPL with (scheme base) and (scheme write)
; libraries already imported (the latter one is only needed for tests).
; The system as implememted here is quite light on optimization and error checking.
; Support for #& read syntax and boxes is commented-out, but, if uncommented, works
; on systems supporting both features (e.g. Chez Scheme).


;
; 1) helper macros, used throughout all parts of the implementation
;

; (classify x if-ellipsis if-underscore if-var if-other)
; returns one of four expressions based on type of x, in 4 steps
; Should work on R7RS, R6RS, and earlier syntax-rules expanders

(define-syntax classify
  (syntax-rules ()
    ((_ (x . y) ke ku kv kf) kf)
    ((_ #(x ...) ke ku kv kf) kf)
    ;((_ #&x ke ku kv kf) kf)
    ((_ atom ke ku kv kf) ; ellipsis test after Taylor Campbell
     (let-syntax ((e? (syntax-rules () ((_ (x atom) t f) t) ((_ x t f) f))))
       (e? (1 2 3) ke (classify-nonellipsis-atom atom ku kv kf))))))

(define-syntax classify-nonellipsis-atom
  (syntax-rules ()
    ((_ atom ku kv kf) ; symbol test after Oleg Kiselyof
     (let-syntax ((s? (syntax-rules () ((_ atom t f) t) ((_ x t f) f))))
       (s? abracadabra (classify-nonellipsis-symbol atom ku kv) kf)))))

(define-syntax classify-nonellipsis-symbol
  (syntax-rules ()
    ((_ symbol ku kv) ; see if symbol acts like a variable
     (let-syntax ((b (syntax-rules () ((_ symbol k t f) (k symbol t f))))
                  (k (syntax-rules () ((_ () t f) t) ((_ x t f) f))))
       (b () k (classify-nonellipsis-var symbol ku kv) ku)))))

(define-syntax classify-nonellipsis-var
  (syntax-rules ()
    ((_ var ku kv) ; needed for R4RS/R5RS systems where _ is a regular var
     (let-syntax ((u? (syntax-rules (var) ((_ var t f) t) ((_ x t f) f))))
       (u? _ ku kv)))))

; check if v is not among vars in (a ...) list, using free-id= rules for comparison
; NB: neither v, nor any of a-s should be ellipsis (...) or underscore (_) identifiers

(define-syntax if-new-var
  (syntax-rules ()
    ((_ v (a ...) kt kf)
     (let-syntax ((ck (syntax-rules (a ...) ((_ a) kf) ... ((_ x) kt)))) (ck v)))))

; calculate set minus on two set of vars, using free-id= rules for comparison
; NB: neither set should contain ellipsis (...) and underscore (_) identifiers

(define-syntax varset-minus
  (syntax-rules () ; (_ v* mv* k () . a*) ==> (k v-mv* . a*)
    ((_ () mv* k rv* . a*) (k rv* . a*))
    ((_ (v . v*) mv* k rv* . a*)
     (if-new-var v mv*
       (varset-minus v* mv* k (v . rv*) . a*)
       (varset-minus v* mv* k rv* . a*)))))

; (replace-specials ell und sexp . k) invokes k with reassembled sexp,
; replacing ... with ell and _ with und (_ and ... are recognized according to the free-id= rules)

(define-syntax replace-specials
  (syntax-rules ()
    ((_ ell und sexp . cont)
     (letrec-syntax
       ((subx
         (syntax-rules ()
           ((_ ev uv () k . a*) (k () . a*))
           ((_ ev uv (x . y)  k . a*) (subx ev uv x subcdr ev uv y k . a*))
           ;((_ ev uv #&x k . a*) (subx ev uv x rebox k . a*))
           ((_ ev uv #(x (... ...)) k . a*) (subx ev uv (x (... ...)) revec k . a*))
           ((_ ev uv x k . a*) (classify x (k ev . a*) (k uv . a*) (k x . a*) (k x . a*)))))
        (subcdr
         (syntax-rules ()
           ((_ sx ev uv y k . a*) (subx ev uv y repair sx k . a*))))
        (repair (syntax-rules () ((_ sy sx k . a*) (k (sx . sy) . a*))))
        ;(rebox  (syntax-rules () ((_ sx k . a*) (k #&sx . a*))))
        (revec  (syntax-rules () ((_ (sx (... ...)) k . a*) (k #(sx (... ...)) . a*)))))
       (subx ell und sexp . cont)))))

; Petrofsky's extraction (after Al* Petrofsky via Oleg Kiselyof)

(define-syntax extract
  (syntax-rules ()
    ((_ _id _x _c)
     (letrec-syntax
       ((tr (syntax-rules (_id)
              ((_ x _id tail (k il . a*)) (k (x . il) . a*))
              ((_ d (x . y) tail c) (tr x x (y . tail) c))
              ((_ d1 d2 () (k il . a*)) (k (_id . il) . a*))
              ((_ d1 d2 (x . y) c) (tr x x y c)))))
       (tr _x _x () _c)))))

(define-syntax extract*
  (syntax-rules ()
    ((_ id* x c) (extract* () id* x c))
    ((_ il () x (k () . a*)) (k il . a*))
    ((_ il (id . id*) x c)
     (extract id x (extract* il id* x c)))))


;
; 2) base matcher macro framework/protocol
;

(define-syntax match
  (syntax-rules ()
    ((_ exp clause ...)
     (let ((xv exp))
       (match-var xv clause ...)))))

; internal macro to jump-start var collection and code generation;
; submatch below accepts only vars as first argument

(define-syntax match-var
  (syntax-rules (=>)
    ((_ xv) (if #f #f))
    ((_ xv (pat (=> nv) exp ...) . clauses)
     (let* ((nv (lambda () (match-var xv . clauses))) (b nv))
       (let-syntax ((n (syntax-rules () ((_ k . a*) (k () . a*)))))
         (submatch xv pat (b n) (let () exp ...) (nv)))))
    ((_ xv (pat (=> nv bv) exp ...) . clauses)
     (let* ((nv (lambda () (match-var xv . clauses))) (bv nv))
       (let-syntax ((n (syntax-rules () ((_ k . a*) (k () . a*)))))
         (submatch xv pat (bv n) (let () exp ...) (nv)))))
    ((_ xv (pat exp ...) . clauses)
     (let* ((next (lambda () (match-var xv . clauses))) (b next))
       (let-syntax ((n (syntax-rules () ((_ k . a*) (k () . a*)))))
         (submatch xv pat (b n) (let () exp ...) (next)))))))

; main var scanner / code generator

; Submatch operates in two modes: as pattern variable scanner and as code generator
; xv is a variable let-bound to the current expression being matched by the pattern
; c is 'context' (as described below, context format depends on mode of operation)
; p is a pattern (either primitive or a macro name followed by args / subpatterns)
; kt is the right-hand-side expr, usually complex, so it shouldn't be duplicated
; kf is the failure expression, usually just a call of a variable, can be duplicated
; - in scanner mode, it is invoked with () for xv and kf parameters and (n) context,
; where n is a macro thunk, returning a list of pairs (var . tmpid), with vars unique
; in free-id=? sense; this list is grown by syntactically rebinding n to a new list
; and expanding kt in its context. The main work is done by submatch, but external
; matchers have to cooperate by calling submatch with their sub-pattern arguments
; - in codegen mode, it is invoked with an id for xv and (b n) context, where n
; is as stated above (except that it assembles a list of vars, with no tempids),
; and b is the name of the lexically closest backtracking point (also a thunk).
; In this mode, submatch'es task is to build the matching code; it does that on
; its own for primitive patterns, but needs cooperation from external matchers for
; all non-primitive patterns

(define-syntax submatch
  (syntax-rules (quote quasiquote)
    ; scan for vars
    ((_ () () (n) kt ()) kt)
    ((_ () (quote lit) (n) kt ()) kt)
    ; generate code
    ((_ xv () c kt kf)
     (if (null? xv) kt kf))
    ((_ xv (quote lit) c kt kf)
     (if (equal? xv (quote lit)) kt kf))
    ((_ xv (quasiquote qq) c kt kf)
     (submatch-qq xv qq c kt kf))
    ((_ xv (h . t) c kt kf)
     (h xv t c kt kf))
    ; scan atom for vars
    ((_ () a (n) kt ())
     (classify a
       (syntax-error "... used as a variable name")
       kt ; _ is not a var
       (let-syntax
         ((k (syntax-rules ()
               ((_ v* t*)
                (if-new-var a v*
                  ; rebind n to a syntax 'thunk' returning extended name-temp alist
                  (let-syntax ((n (syntax-rules () ((_ k . args) (k (a . v*) (t . t*) . args)))))
                    kt)
                  kt)))))
         (n k))
       kt))
    ; generate atom code
    ((_ xv a (b n) kt kf)
     (classify a
       (syntax-error "... used as a variable name")
       kt ; _ matches anything
       (let-syntax
         ((k (syntax-rules ()
               ((_ v*)
                (if-new-var a v*
                  (let ((a xv))
                    ; rebind n to a syntax 'thunk' returning extended name list
                    (let-syntax ((n (syntax-rules () ((_ k . args) (k (a . v*) . args)))))
                      kt))
                  (if (equal? xv a) kt kf)))))) ; non-linear check ror repeated vars
         (n k))
       (if (equal? xv (quote a)) kt kf)))))

; quasiquote matcher expands into a combination of specific matchers defined below;
; multiple splicing patterns at the same level do greedy matching, maximizing lengths
; of left/upstream segments; other 'solutions' can be obtained via backtracking

(define-syntax submatch-qq
  (syntax-rules (unquote unquote-splicing)
    ((_ xv ,p c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (,@lp) c kt kf)
     (submatch xv lp c kt kf))
    ((_ xv (,@lp . dp) c kt kf)
     (submatch xv (~append lp `dp) c kt kf))
    ((_ xv (ap . dp) c kt kf)
     (submatch xv (~cons `ap `dp) c kt kf))
    ((_ xv #(p ...) c kt kf)
     (submatch xv (~list->vector `(p ...)) c kt kf))
    ;((_ xv #&p c kt kf)
    ; (submatch xv (~box `p) c kt kf))
    ((_ xv lit c kt kf)
     (submatch xv (quote lit) c kt kf))))

; pattern var scanner -- uses var extraction protocol (submatch) and Petrofsky's extractor;
; var extraction protocol returns arbitrarily colored vars, distinct w.r.t free-id=?;
; Petrofsky's extractor locates their pattern-colored versions suitable for binding.
; It wouldn't be necessary if not for ~or and ~etc matchers that need to bind all vars
; NB: The extractor can't accidentally hit on a non-pattern identifier because we explicitly
; prohibit use of pattern variables in non-pattern subelements of patterns

(define-syntax extract-pattern-vars
  (syntax-rules () ; (_ p (rk . a*)) ==> (rk v* t* . a*)
    ((_ p (rk . a*))
     (let-syntax ((n (syntax-rules () ((_ k . args) (k () () . args)))))
       (submatch () p (n) ; scan for vars protocol
         (let-syntax
           ((k (syntax-rules ()
                 ((_ v* t*) (extract-pattern-vars p v* t* (rk . a*))))))
           (n k))
         ())))
     ((_ p v* t* (rk . a*)) ; rescan to get colors right (in bound-id=? sense)
      (extract* v* p (rk () t* . a*)))))

(define-syntax extract-new-pattern-vars
  (syntax-rules () ; (_ p n (rk . a*)) ==> (rk () nv* . a*)
    ((_ pat names cont)
     (letrec-syntax
       ((step1 (syntax-rules () ((_ mv* p c) (extract-pattern-vars p (step2 mv* c)))))
        (step2 (syntax-rules () ((_ v* t* mv* c) (varset-minus v* mv* step3 () c))))
        (step3 (syntax-rules () ((_ v-mv* (rk . a*)) (rk () v-mv* . a*)))))
       (names step1 pat cont)))))

;
; 3) matchers used by quasiquote notation
;

(define-syntax ~cons
  (syntax-rules ()
    ((_ () (ap dp) (n) kt ()) ; scan ap, dp for vars
     (submatch () ap (n) (submatch () dp (n) kt ()) ()))
    ((_ xv (ap dp) c kt kf)
     (if (pair? xv)
         (let ((axv (car xv)) (dxv (cdr xv)))
           (submatch axv ap c (submatch dxv dp c kt kf) kf))
         kf))))

(define-syntax ~list
  (syntax-rules ()
    ((_ xv () c kt kf)
     (submatch xv '() c kt kf))
    ((_ xv (p . p*) c kt kf)
     (submatch xv (~cons p (~list . p*)) c kt kf))))

(define-syntax ~list->vector
  (syntax-rules ()
    ((_ () (p) (n) kt ()) ; scan for vars
     (submatch () p (n) kt ()))
    ((_ xv (p) c kt kf)
     (if (vector? xv)
         (let ((yv (vector->list xv))) (submatch yv p c kt kf))
         kf))))

(define (match:append-greedy-start xv try) ; internal
  (let loop ((txv xv) (rxv '()))
    (if (pair? txv) (loop (cdr txv) (cons (car txv) rxv)) (try rxv txv))))

(define-syntax ~append
  (syntax-rules ()
    ((_ () p* (n) kt ()) ; scan for vars
     (submatch () (~and . p*) (n) kt ())) ; union
    ((_ xv () c kt kf)
     (submatch xv '() c kt kf))
    ((_ xv (p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (hp tp) (b n) kt kf)
     (let ((f (lambda () kf))) ; in scope of 'parent' b
       (define (try rxv txv)
         (define (b) (if (pair? rxv) (try (cdr rxv) (cons (car rxv) txv)) (f)))
         (let ((hxv (reverse rxv))) ; match head first
           (submatch hxv hp (b n) (submatch txv tp (b n) kt (b)) (b))))
       (match:append-greedy-start xv try)))
    ((_ xv (p . p*) c kt kf)
     (submatch xv (~append p (~append . p*)) c kt kf))))

;(define-syntax ~box
;  (syntax-rules ()
;    ((_ () (p) (n) kt ()) ; scan for vars
;     (submatch () p (n) kt ()))
;    ((_ xv (p) c kt kf)
;     (if (box? xv)
;        (let ((yv (unbox xv))) (submatch yv p c kt kf))
;        kf))))


;
; 4) additional useful matchers, going beyond common core specified by SRFI-200
;

; 'value' matcher compares xv with the value of runtime-calculated expression via equal?

(define-syntax ~value
  (syntax-rules ()
    ((_ () (e) (n) kt ()) kt) ; scan for vars
    ((_ xv (e) c kt kf) (if (equal? xv e) kt kf))))


; non-greedy matcher for (possibly improper) lists

(define-syntax ~append/ng
  (syntax-rules ()
    ((_ () p* (n) kt ()) ; scan for vars
     (submatch () (~and . p*) (n) kt ())) ; union
    ((_ xv () c kt kf)
     (submatch xv '() c kt kf))
    ((_ xv (p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (hp tp) (b n) kt kf)
     (let ((f (lambda () kf))) ; in scope of 'parent' b
       (let loop ((hxv '()) (txv xv)) ; match head first
         (define (b) (if (pair? txv) (loop (append hxv (list (car txv))) (cdr txv)) (f)))
         (submatch hxv hp (b n) (submatch txv tp (b n) kt (b)) (b)))))
    ((_ xv (p . p*) c kt kf)
     (submatch xv (~append/ng p (~append/ng . p*)) c kt kf))))

; non-iterative matcher for append with fixed-length rhs list (first arg, may be improper)
; may be used to implement single-ellipsis append patterns as popularized by syntax-rules

(define (match:append-tail-length l)
  (let loop ((l l) (n 0))
    (if (pair? l) (loop (cdr l) (+ n 1)) n)))

(define (match:append-tail-start xv n fail try) ;=> (try head tail) or (fail)
  (let loop ((l xv) (n n))
    (if (zero? n)
        (let loop ((lag xv) (lead l) (head '()))
          (if (pair? lead)
              (loop (cdr lag) (cdr lead) (cons (car lag) head))
              (try (reverse head) lag)))
        (if (pair? l) (loop (cdr l) (- n 1)) (fail)))))

(define-syntax ~append/t
  (syntax-rules ()
    ((_ () (t hp tp) (n) kt ()) ; scan for vars
     (submatch () (~and hp tp) (n) kt ())) ; union
    ((_ xv (t hp tp) c kt kf)
     (let ((f (lambda () kf)))
       (match:append-tail-start xv (if (integer? 't) 't (match:append-tail-length 't)) f
         (lambda (hxv txv) (submatch hxv hp c (submatch txv tp c kt (f)) (f))))))))

; general-purpose parameterized backtracking matcher

; (~iterate start head tail v* p) builds a backtracking matcher
; that produces a stream of 'solutions' to be matched against p;
; v* is a list of state variables (names mostly used for exposition)
; - start is invoked with original value and two continuation procedures:
; first one accepts 'seed' values for state variables if start succeeds,
; the second one accepts no values and is called if start fails
; - head accepts current values of state variables and returns a
; single value to be matched against pattern p
; - tail accepts the same two continuations as start, followed by
; the current values of state variables; it should either call its
; first continuation to continue with new values of state vars,
; or the second one to signal that there are no more 'solutions'
; note: start head tail can be procedures add/or macros
; note: both try and f should be called in tail positions!
(define-syntax ~iterate
  (syntax-rules ()
    ; scan for vars
    ((_ () (start head tail v* p) (n) kt ())
     (submatch () p (n) kt ()))
    ; generate code
    ((_ xv (start head tail v* p) (b n) kt kf)
     (let ((f (lambda () kf))) ; in scope of 'parent' b
       (define (try . v*)
         (define (b) (tail try f . v*))
         (let ((mxv (head . v*)))
           (submatch mxv p (b n) kt (b))))
       (start xv try f)))))


; 'popular' parameterized matchers for vector-like sequences

(define-syntax ~seq-append
  (syntax-rules ()
    ((_ () (x? x-length subx nullx . p*) (n) kt ()) ; scan for vars
     (submatch () (~and . p*) (n) kt ()))
    ((_ xv (x? x-length subx nullx) c kt kf)
     (submatch xv nullx c kt kf))
    ((_ xv (x? x-length subx nullx p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (x? x-length subx nullx hp tp) (b n) kt kf)
     (let ((l (x-length xv)) (f (lambda () kf)))
       (let loop ((i l))
         (define (b) (if (> i 0) (loop (- i 1)) (f)))
         (let ((hxv (subx xv 0 i))) ; match head first
           (submatch hxv hp (b n)
             (let ((txv (subx xv i l)))
               (submatch txv tp (b n) kt (b))) (b))))))
  ((_ xv (x? x-length subx nullx p . p*) c kt kf)
   (submatch xv (~seq-append x? x-length subx nullx p
      (~seq-append x? x-length subx nullx . p*)) c kt kf))))

(define-syntax ~seq-append/ng
  (syntax-rules ()
    ((_ () (x? x-length subx nullx . p*) (n) kt ()) ; scan for vars
     (submatch () (~and . p*) (n) kt ()))
    ((_ xv (x? x-length subx nullx) c kt kf)
     (submatch xv nullx c kt kf))
    ((_ xv (x? x-length subx nullx p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (x? x-length subx nullx hp tp) (b n) kt kf)
    (let ((l (x-length xv)) (f (lambda () kf)))
      (let loop ((i 0))
        (define (b) (if (< i l) (loop (+ i 1)) (f)))
        (let ((hxv (subx xv 0 i))) ; match head first
          (submatch hxv hp (b n)
            (let ((txv (subx xv i l)))
              (submatch txv tp (b n) kt (b))) (b))))))
  ((_ xv (x? x-length subx nullx p . p*) c kt kf)
   (submatch xv (~seq-append/ng x? x-length subx nullx p
      (~seq-append/ng x? x-length subx nullx . p*)) c kt kf))))


;
; 5) boolean matchers
;

; 'and'-matcher (all pattern vars are bound in the rest of the patterns)

(define-syntax ~and
  (syntax-rules ()
    ((_ xv () c kt kf)
     kt)
    ((_ xv (p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (p . p*) c kt kf)
     (submatch xv p c (submatch xv (~and . p*) c kt kf) kf))))

; 'or'-matcher (on success, all pattern vars are bound to #f except for those in the matching case)

(define-syntax ~or
  (syntax-rules ()
    ((_ () p* (n) kt ()) ; scan for vars
     (submatch () (~and . p*) (n) kt ())) ; union
    ((_ xv () c kt kf)
     kf)
    ((_ xv (p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv p* (b n) kt kf)
     (extract-new-pattern-vars (~and . p*) n (~or xv p* (b n) kt kf)))
    ((_ () (v ...) xv p* c kt kf)
     (let ((v #f) ... (lkt (lambda (v ...) kt)))
       (submatch xv (match:or-aux . p*) c (lkt v ...) kf)))))

(define-syntax match:or-aux ; helper for ~or
  (syntax-rules ()
    ((_ xv () c kt kf)
     kf)
    ((_ xv (p) c kt kf)
     (submatch xv p c kt kf))
    ((_ xv (p . p*) (b n) kt kf) ; kt can be duplicated
     (let ((b (lambda () (submatch xv (match:or-aux . p*) (b n) kt kf)))) ; in scope of 'parent' b
       (submatch xv p (b n) kt (b))))))

; 'not'-matcher (no additional pattern vars, if present, are bound in the rest of the patterns)

(define-syntax ~not
  (syntax-rules ()
    ((_ () p* (n) kt ()) kt) ; scan for vars: no vars escape
    ((_ xv (p) c kt kf)
     (let ((t (lambda () kt)) (f (lambda () kf)))
       (submatch xv p c (f) (t))))
    ((_ xv (p ...) c kt kf)
     (submatch xv (~and (~not p) ...) c kt kf))))


;
; 6)  ~etc: ... - like list matchers
;

; Nonlinear part of ~etc works as follows: code for p is generated in
; empty 'n' (i.e. we skip nonlinear checks against vars on the left);
; when all p's own vars are bound to full lists, a precondition code
; is built that compares their values with the existing values of
; common variables of p and patterns upstream and triggers a failure
; if they are different; then the 'n' lists are merged for the patterns
; downstream (this part is easy -- just scan p in the usual manner)

(define-syntax match:etc-nl-test
  (syntax-rules ()
    ((_ ov* () () e*) (and . e*))
    ((_ ov* (iv . iv*) (it . it*) e*)
     (if-new-var iv ov*
       (match:etc-nl-test ov* iv* it* e*)
       (match:etc-nl-test ov* iv* it*
         ((equal? iv (reverse it)) . e*))))))

(define-syntax ~etc
  (syntax-rules ()
    ((_ () (p) (n) kt ()) ; scan for vars
     (submatch () p (n) kt ()))
    ((_ xv (p) c kt kf)
     (extract-pattern-vars p (~etc xv p c kt kf)))
    ((_ (v ...) (t ...) xv p (b n) kt kf)
     (let loop ((lxv xv) (t '()) ...)
       (cond ((null? lxv)
              (if (n match:etc-nl-test (v ...) (t ...) ())
                  (let ((v (reverse t)) ...) kt)
                  kf))
             ((pair? lxv)
              (let ((axv (car lxv)) (dxv (cdr lxv)))
                (let-syntax ((n (syntax-rules () ((_ k . a*) (k () . a*)))))
                  (submatch axv p (b n) (loop dxv (cons v t) ...) kf))))
             (else kf))))))

(define-syntax ~etcse ; sine errore
  (syntax-rules ()
    ((_ () (p) (n) kt ()) ; scan for vars
     (submatch () p (n) kt ()))
    ((_ xv (p) c kt kf)
     (extract-pattern-vars p (~etcse xv p c kt kf)))
    ((_ (v ...) (t ...) xv p (b n) kt kf)
     (let loop ((lxv xv) (t '()) ...)
       (cond ((null? lxv)
              (if (n match:etc-nl-test (v ...) (t ...) ())
                  (let ((v (reverse t)) ...) kt)
                  kf))
             ((pair? lxv)
              (let ((axv (car lxv)) (dxv (cdr lxv)))
                (let-syntax ((n (syntax-rules () ((_ k . a*) (k () . a*)))))
                  (submatch axv p (b n) ; just skip failed submatches
                    (loop dxv (cons v t) ...) (loop dxv t ...)))))
             (else kf))))))


;
; 7) general-purpose matchers with a function/predicate parameter
;

; 'property access' matcher: when matching x,
; (~prop f => p ...)            matches the result(s) of (f x) to p ...
; (~prop f (arg ...) => p ...)  matches the result(s) of (f x arg ...) to p ...
(define-syntax ~prop
  (syntax-rules (=>)
    ; scan for vars
    ((_ () (x->y => . p*)         (n) kt ()) (submatch () (~and . p*) (n) kt ()))
    ((_ () (x->y (a ...) => . p*) (n) kt ()) (submatch () (~and . p*) (n) kt ()))
    ; generate code
    ((_ xv (x->y => p) c kt kf)
     (let ((yv (x->y xv)))
       (submatch yv p c kt kf)))
    ((_ xv (x->y => . p*) c kt kf)
     (let ((yv (call-with-values (lambda () (x->y xv)) list)))
       (submatch yv (~list . p*) c kt kf)))
    ((_ xv (x->y (a ...) => p) c kt kf)
     (let ((yv (x->y xv a ...)))
       (submatch yv p c kt kf)))
    ((_ xv (x->y (a ...) => . p*) c kt kf)
     (let ((yv (call-with-values (lambda () (x->y xv a ...)) list)))
       (submatch yv (~list . p*) c kt kf)))))

; 'predicate test' matcher: when matching x,
; (~test f)                     fails if (f x) returns #f
; (~test f (arg ...))           fails if (f x arg ...) returns #f
; (~test f => p)                fails if (f x) returns #f, otherwise matches result to p
; (~test f (arg ...) => p)      fails if (f x) returns #f, otherwise matches result to p
(define-syntax ~test
  (syntax-rules (=>)
    ; scan for vars
    ((_ () (x?)              (n) kt ()) kt)
    ((_ () (x? (a ...))      (n) kt ()) kt)
    ((_ () (x? => p)         (n) kt ()) (submatch () p (n) kt ()))
    ((_ () (x? (a ...) => p) (n) kt ()) (submatch () p (n) kt ()))
    ; generate code
    ((_ xv (x?) c kt kf)
     (if (x? xv) kt kf))
    ((_ xv (x? (a ...)) c kt kf)
     (if (x? xv a ...) kt kf))
    ((_ xv (x? => p) c kt kf)
     (let ((v (x? xv))) (if v (submatch v p c kt kf) kf)))
    ((_ xv (x? (a ...) => p) c kt kf)
     (let ((v (x? xv a ...))) (if v (submatch v p c kt kf) kf)))))


;
; 8) special matchers serving as building blocks for custom matchers
;

; 'literal check' matcher : (~if-id-member a (l ...) pt pf)
; uses pt if a is in (l ...), pf otherwise; uses free-id=? rules
(define-syntax ~if-id-member
  (syntax-rules ()
    ((_ xv (a (l ...) pt pf) c kt kf)
     (classify a
       (syntax-error "... used as a variable name")
       (syntax-error "_ used as a variable name")
       (if-new-var a (l ...) (submatch xv pf c kt kf) (submatch xv pt c kt kf))
       (submatch yv pt c kt kf)))))

; (~replace-specials new-ellipsis new-underscore p) matches against p after replacing
; ... in p with new-ellipsis and _ with new-underscore
(define-syntax ~replace-specials
  (syntax-rules ()
    ((_ xv (ne nu p) c kt kf)
     (replace-specials ne nu p ~replace-specials #f xv c kt kf))
    ((_ newp #f xv c kt kf)
     (submatch xv newp c kt kf))))

; 'cut' matcher (does not allow backtracking into p)
(define-syntax ~cut!
  (syntax-rules ()
    ((_ () (p) (n) kt ()) ; scan for vars
     (submatch () p (n) kt ()))
    ((_ xv (p) (b n) kt kf)
     (let ((b! b)) (submatch xv p (b n) (let ((b b!)) kt) kf)))))


;
; 9) extending the matcher
;

(define-syntax define-match-pattern
  (syntax-rules ()
    ((_ ~dm (l ...) ((* . args) p) ...)
     (define-syntax ~dm
       (syntax-rules (l ...)
         ((_ xv args c kt kf)
          (submatch xv p c kt kf)) ...)))))

(define-syntax define-record-match-pattern
  (syntax-rules ()
    ((_ (~name v ...) pred? (v1 acc . _) ...)
     (define-match-pattern ~name ()
       ((_ v ...) (~and (~test pred?) (~prop acc => v1) ...))))))

; NB: all new matchers below are defined via define-match-pattern (no more submatch/hand-coding)


;
; 10) convenience matchers for popular scheme data types
;

; these two matchers are already defined in section 3) :
; (define-match-pattern ~box () ((_ p) (~and (~test box?) (~prop unbox => p))))
; (define-match-pattern ~list->vector () ((_ p) (~and (~test vector?) (~prop vector->list => p))))

(define-match-pattern ~null?            () ((_ p ...) (~and (~test null?)    p ...)))
(define-match-pattern ~pair?            () ((_ p ...) (~and (~test pair?)    p ...)))
(define-match-pattern ~list?            () ((_ p ...) (~and (~test list?)    p ...)))
(define-match-pattern ~boolean?         () ((_ p ...) (~and (~test boolean?) p ...)))
(define-match-pattern ~number?          () ((_ p ...) (~and (~test number?)  p ...)))
(define-match-pattern ~integer?         () ((_ p ...) (~and (~test integer?) p ...)))
(define-match-pattern ~vector?          () ((_ p ...) (~and (~test vector?)  p ...)))
(define-match-pattern ~string?          () ((_ p ...) (~and (~test string?)  p ...)))
(define-match-pattern ~symbol?          () ((_ p ...) (~and (~test symbol?)  p ...)))
(define-match-pattern ~char?            () ((_ p ...) (~and (~test char?)    p ...)))
;(define-match-pattern ~box?             () ((_ p ...) (~and (~test box?)     p ...)))

(define-match-pattern ~vector->list     () ((_ p)     (~and (~test list?)   (~prop list->vector => p))))
(define-match-pattern ~string->list     () ((_ p)     (~and (~test list?)   (~prop list->string => p))))
(define-match-pattern ~list->string     () ((_ p)     (~and (~test string?) (~prop string->list => p))))
(define-match-pattern ~string->symbol   () ((_ p)     (~and (~test symbol?) (~prop symbol->string => p))))
(define-match-pattern ~symbol->string   () ((_ p)     (~and (~test string?) (~prop string->symbol => p))))

(define-match-pattern ~vector           () ((_ p ...) (~and (~test vector?) (~prop vector->list => (~list p ...)))))
(define-match-pattern ~string           () ((_ p ...) (~and (~test string?) (~prop string->list => (~list p ...)))))

(define-match-pattern ~string-append    () ((_ p ...) (~seq-append    string? string-length substring "" p ...)))
(define-match-pattern ~string-append/ng () ((_ p ...) (~seq-append/ng string? string-length substring "" p ...)))
(define-match-pattern ~vector-append    () ((_ p ...) (~seq-append    vector? vector-length vector-copy '#() p ...)))
(define-match-pattern ~vector-append/ng () ((_ p ...) (~seq-append/ng vector? vector-length vector-copy '#() p ...)))

(define-match-pattern ~number->string   () ((_ p)     (~and (~test string?) (~prop string->number => p)))
                                           ((_ p rx)  (~and (~test string?) (~prop string->number (rx) => p))))
(define-match-pattern ~string->number   () ((_ p)     (~and (~test number?) (~prop number->string => p)))
                                           ((_ p rx)  (~and (~test number?) (~prop number->string (rx) => p))))

;
; 11) additional convenience/compatibility matchers
;

; WCS-like = property matcher
(define-match-pattern ~= ()
  ((~= f p) (~prop f => p)))

; WCS-like ? predicate matcher
(define-match-pattern ~? ()
  ((~? f p ...) (~and (~test f) p ...)))


; Racket-like list* (a.k.a. cons*)

(define-match-pattern ~list* ()
  ((~list* p) p)
  ((~list* p . p*) (~cons p (~list* . p*))))

; Racket-like list-no-order

(define-syntax match:cno-start
  (syntax-rules () ((_ xv try f) (if (pair? xv) (try '() xv) (f)))))

(define-syntax match:cno-head
  (syntax-rules () ((_ h t) (cons (car t) (append h (cdr t))))))

(define-syntax match:cno-tail
  (syntax-rules () ((_ try f h t) (if (pair? (cdr t)) (try (cons (car t) h) (cdr t)) (f)))))

(define-match-pattern ~cons-no-order ()
  ((~cons-no-order pe pr)
   (~iterate match:cno-start match:cno-head match:cno-tail (h t) (~cons pe pr))))

(define-match-pattern ~list-no-order ()
  ((~list-no-order) '())
  ((~list-no-order p) (~list p))
  ((~list-no-order p . p*) (~cons-no-order p (~list-no-order . p*))))

(define-match-pattern ~list-no-order* ()
  ((~list-no-order* p) p)
  ((~list-no-order* p . p*) (~cons-no-order p (~list-no-order* . p*))))



;========================================================================================
;
;  Complementary pieces of templating
;
;========================================================================================

; By construction, patterns resemble corresponding Scheme constructors, and can be
; combined in the same way, so regular base Scheme already supplies cons, list, and
; scores of other functions that re-construct what similar-looking patterns de-construct:
;
; pattern: (~list (~cons a b))   template (regular Scheme): (list (cons a b))
;
; This proposal's quasiquote patterns also mirror regular Scheme's quasiquote templates:
;
; pattern: `(,(~cons a b))   template (regular Scheme): `(,(cons a b))
; pattern: `(,@a ,@b)        template (regular Scheme): `(,@a ,@b)
;
; This correspondence is not designed to be 1-to-1, because needs of patterns and Scheme
; 'templates', i.e. constructor expressions are different. Still, there are pieces of the
; pattern language that call for equally expressive template forms. In particular, one
; may find it convenient to have a templating counterpart to ~etc patterns.
;
; Unlike patterns though, the choice of regular scheme expressions for templating does
; not allow us to collect what would act as template variables easily -- procedures
; won't cooperate. What we can do is to limit subforms of 'etc' templates, using a
; restricted grammar that makes this possible:
;
; <template expression> -> <value expression> | <etc expression> | <expression>
;
; <value expression> -> (value <expression>)
;
; <etc expression> -> (etc <template>)
;
;    <template> ->
;     <template var>      ; symbol
;   | <constant>          ; char, string, number, ...
;   | (quote <datum>)
;   | (value <expression>)
;   | (<name> <template> ...)
;
; NB: <name> should be restricted to names of forms that have expressions as subforms;
; this disqualify forms like lambda, let, do, forms with internal definitions etc.
;
; This restricted form allows scanning for template vars due to its limited nature.
; Scanning of <etc expression> should produce one or more template vars, which are
; expected to be lists of the same length at runtime, so the following transformation
; can produce the actual output expression when 'etc' form is macroexpanded:
;
; (etc (list x* y* (value foo))) ==> (map (lambda (x* y*) (list x* y* foo)) x* y*)
;
; Note that (value x) parts, not scanned for template vars, are just replicated.
; In all other respects, value is just the identity macro.

(define-syntax value ; need to be imported together with etc
  (syntax-rules () ((_ x) x)))

; scanning for template vars

(define-syntax extract-template-vars
  (syntax-rules () ; (_ t rk . a*) => (rk v* . a*)
    ((_ tpl . cont)
     (letrec-syntax
       ((err
         (syntax-rules ()
           ((_ t) (syntax-error "etc: invalid template" t))))
        (ext
         (syntax-rules (quote value) ; quasiquote
           ((_ (quote x)      k . a*) (k () . a*))
           ((_ (value x)      k . a*) (k () . a*))
           ((_ ()             k . a*) (err ()))
           ((_ (n)            k . a*) (k () . a*))
           ((_ (n t)          k . a*) (ext t k . a*))
           ((_ (n t . t*)     k . a*) (ext t extcdr (n . t*) k . a*))
           ;((_ #&x            k . a*) (err #&x))
           ((_ #(x (... ...)) k . a*) (err #(x (... ...))))
           ((_ x              k . a*)
            (classify x (err x) (err x) (k (x) . a*) (k () . a*)))))
        (extcdr
         (syntax-rules ()
           ((_ v* t k . a*) (ext t merge v* k . a*))))
        (merge
         (syntax-rules ()
           ((_ () rv*         k . a*) (k rv* . a*))
           ((_ (v . v*) rv*   k . a*)
            (if-new-var v rv* (merge v* (v . rv*) k . a*) (merge v* rv* k . a*))))))
       (ext tpl . cont)))))

; expander for (etc <template>)

(define-syntax etc
  (syntax-rules ()
    ((_ t)
     (classify t
       (syntax-error "etc: ... used as a template variable")
       (syntax-error "etc: _ used as a template variable")
       t ; optimization: for template var t, (etc t) ==> t
       (extract-template-vars t etc t)))
    ((_ () t) (syntax-error "etc: no template variables" t))
    ((_ (v ...) t) (map (lambda (v ...) t) v ...))))




;========================================================================================
;
;  Tests (borrowed from many sources)
;
;========================================================================================

; simple test machinery (avp)

(define *errors* 0)

(define (test-matcher matcher t*)
  (let ((count 0))
    (for-each (lambda (l&r)
                (let* ((in (car l&r))
                       (ex (cadr l&r))
                       (rv (matcher in)))
                  (if (equal? rv ex) (begin (display "ok : ") (write in))
                      (begin (set! count (+ 1 count))
                             (display "ERROR on ") (write in)
                             (display ", returned ") (write rv)
                             (display ", expected ") (write ex)))
                  (newline)))
              t*)
    (cond
     ((zero? count) (display "all tests passed\n"))
     (else (set! *errors* (+ *errors* count))
           (display (number->string count))
           (display " ERRORS\n")))))

(define (test-restart matcher in out)
  (let ((v '()))
    (matcher in (lambda (x) (display "K: ") (write x) (newline) (set! v (cons x v))))
    (set! v (reverse v))
    (cond
      ((equal? out v) (display "ok : ") (write in) (newline))
      (else (set! *errors* (+ *errors* 1))
            (display "ERROR : ") (write in) (newline)
            (display "   result ") (write v) (newline)
            (display "   expect ") (write out) (newline)))))

; tests

; simple matches
(display "\nsimple matcher-1\n")
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
  '((1                          number-one)
    (a                          symbol-a)
    (((x y) q)                  (list (x y) q))
    (((a 2) (b a))              (head&tail a 2 b))
    ((+ 0 (+ y z) (+ y z))      (* 2 (+ y z)))
    ((+ (sin a b) (cos a b))    ((+ sin cos) a b))
    ((** 2 4)                   16)
    ((** 2 a)                   (generic (** 2 a)))))

; rollback to the next rule
(display "\nmatcher-2\n")
(define (matcher-2 x k)
  (match x
    (`(,@a ,(~symbol? b) ,@c) (=> next) (k `(p1 ,a ,b ,c)) (next))
    (`(,@a ,@c ,x)            (=> next) (k `(p2 ,a ,c ,x)) (next))
    (x                       (k `(p3 ,x)))))

(test-restart matcher-2
  '(1 2 3 a 4 5)
  '((p1 (1 2 3) a (4 5))
    (p2 (1 2 3 a 4) () 5)
    (p3 (1 2 3 a 4 5))))

; rollback to the next match
(display "\nmatcher-3\n")
(define (matcher-3 x k)
  (match x
    (`(,@a ,b ,@c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (`(,@a ,@c)    (=> next back) (k `(snd ,a ,c)) (back))
    (`,x               (k `(final ,x)))))

(test-restart matcher-3
  '(1 2 3 4 5)
  '((fst (1 2 3 4) 5 ())
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
    (final (1 2 3 4 5))))


; rollback to the next match, constructor syntax
(display "\nmatcher-4\n")
(define (matcher-4 x k)
  (match x
    ((~append a (~list b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~append a c)           (=> next back) (k `(snd ,a ,c)) (back))
    (x                       (k `(final ,x)))))

(test-restart matcher-4
  '(1 2 3 4 5)
  '((fst (1 2 3 4) 5 ())
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
    (final (1 2 3 4 5))))

; same, but with strings
(display "\nmatcher-5\n")

(define (matcher-5 x k)
  (match x
    ((~string-append a (~string b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~string-append a c)             (=> next back) (k `(snd ,a ,c)) (back))
    (x                                (k `(final ,x)))))

(test-restart matcher-5
  "12345"
  '((fst "1234" #\5 "")
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
    (final "12345")))

(define (matcher-5ng x k)
  (match x
    ((~string-append/ng a (~string b) c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    ((~string-append/ng a c)             (=> next back) (k `(snd ,a ,c)) (back))
    (x                                           (k `(final ,x)))))

(test-restart matcher-5ng
  "12345"
  '((fst "" #\1 "2345")
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
    (final "12345")))

(display "\nnonlinear matcher-6\n")
(define (string-reverse s) (list->string (reverse (string->list s))))
(define (matcher-6 x k)
  (match x
    ((~string-append a b a) (=> next back) (k `(rep ,a ,b ,a)) (back))
    ((~string-append a b (~= string-reverse a)) (=> next back) (k `(rev ,a ,b ,(string-reverse a))) (back))
    (x (k `(final ,x)))))

(test-restart matcher-6
  "abracadarba"
  '((rep "a" "bracadarb" "a")
    (rep "" "abracadarba" "")
    (rev "abra" "cad" "arba")
    (rev "abr" "acada" "rba")
    (rev "ab" "racadar" "ba")
    (rev "a" "bracadarb" "a")
    (rev "" "abracadarba" "")
    (final "abracadarba")))

; advanced non-iterative matches
(display "\nadvanced matcher-7\n")

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
  '((1                          number-1-3)
    (2                          number-1-3)
    (4                          (other 4))
    (a                          symbol-a-c)
    (z                          symbol-other)
    (#\z                        char)
    ((a 1)                      (list-a-* (a 1) 1))
    ((1 2 3)                    (list-of-3 (1 2 3)))
    ((1 2 3 4)                  (list-of-4 (1 2 3 4)))
    ((1 2 3 4 5)                (list-of-5 (1 2 3 4 5)))
    ((1 2 3 4 5 6)              (list-of-not-3 (1 2 3 4 5 6)))
    ))

; tests for ~list-no-order / ~list-no-order*

(display "\nmatcher-lno\n")
(define (matcher-lno x k)
  (match x
    ((~list-no-order a b c) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-lno
  '(1 2 3)
  '((fst 1 2 3)
    (fst 1 3 2)
    (fst 2 1 3)
    (fst 2 3 1)
    (fst 3 2 1)
    (fst 3 1 2)
    (final (1 2 3))))

(display "\nmatcher-lno*\n")
(define (matcher-lno* x k)
  (match x
    ((~list-no-order* a b (~etc (~list c))) (=> next back) (k `(fst ,a ,b ,c)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-lno*
  '((1) (2) (3) (4))
  '((fst (1) (2) (3 4))
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
    (final ((1) (2) (3) (4)))))

; tests for ~or

(display "\nmatcher-or\n")

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
  '((1                          number-1-3)
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
    ((foo bar (align 16) baz)   (foo bar 16 baz))
    ))

(define (matcher-or2 x k)
  (match x
    (`(,@a ,(~and b (~or 'b 'c)) ,@c)          (=> next back) (k `(p1 ,a ,b ,c)) (back))
    (`(,@a ,@(~and b (~or '() '(d))) ,@c)      (=> next back) (k `(p2 ,a ,b ,c)) (back))
    (x                                         (k `(p3 ,x)))))

(display "\nmatcher-or bt test\n")
(test-restart matcher-or2
  '(1 a 2 b 3 c 4 d 5)
  '((p1 (1 a 2 b 3) c (4 d 5))
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
    (p3 (1 a 2 b 3 c 4 d 5))))

; tests for ~etc and etc

(display "\nmatcher-etc test\n")
(define (matcher-etc x)
  (match x
    ((~append (~etc (~cons x y)) (~pair? (~etc (~number? z))))          `(first ,x ,y ,z))
    ((~append (~etc (~cons x (~append (~etc y) '()))) '())              `(second ,x ,y))
    ((~cons (~etc (~symbol? x)) (~etc (~cons x y)))                     `(third ,x ,y))
    ((~cons (~and x (~etc (~number?))) (~append (~etc (~cons x y)) z))  `(fourth ,x ,y ,z))
    ((~append (~pair? (~etc (~pair? x))) (~cons y _))                   `(fifth ,x ,y))
    (_                                                                  `(other))))

(test-matcher matcher-etc
  '((((1) (2) (3 . 4) 5 6)                      (first (1 2 3) (() () 4) (5 6)))
    (((a b c d) (e f g) (h i) (j))              (second (a e h j) ((b c d) (f g) (i) ())))
    (((a b c) (a . 2) (b . 3) (c . 4))          (third (a b c) (2 3 4)))
    (((2 3) (2) (3 . 4) (5 . 6))                (fourth (2 3) (() 4) ((5 . 6))))
    (((2 3) (1 . 2) (1 . 3) (1 . 4))            (fifth ((2 3) (1 . 2) (1 . 3)) (1 . 4)))
    ((1 (1 . 2) (1 . 3) (2 . 6))                (other))))

(define *foobar* 42)

(define (matcher-etcetc x)
  (match x
    ((~etc (~list* 1 x y))     (cons 'first (etc (list (value *foobar*) y x))))
    ((~etc (~etc (~list x y))) (cons 'second (etc (etc (list y x)))))
    ((~etc (~cons x y))        (cons 'third (list (etc (cons x x)) (etc (cons y 4)))))
    (_                         (value '(other)))))

(test-matcher matcher-etcetc
  '((((1 1) (1 2) (1 3 4))                      (first (42 () 1) (42 () 2) (42 (4) 3)))
    ((((a b) (c d)) ((e f) (g h) (i j)) ())     (second ((b a) (d c)) ((f e) (h g) (j i)) ()))
    (((a b c) (a . 2) (b . 3) (c . 4))          (third ((a . a) (a . a) (b . b) (c . c)) (((b c) . 4) (2 . 4) (3 . 4) (4 . 4))))
    ((1 (1 . 2) (1 . 3) (2 . 6))                (other))))


; tests for ~cut! matcher

(display "\nmatcher-nocut\n")
(define (matcher-nocut x k)
  (match x
    ((~append a (~cons (~append b c) d)) 
     (=> next back) (k `(fst ,a ,b ,c ,d)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-nocut
  '((1) (2 3) (4))
  '((fst ((1) (2 3)) (4) () ())
    (fst ((1) (2 3)) () (4) ())
    (fst ((1)) (2 3) () ((4)))
    (fst ((1)) (2) (3) ((4)))
    (fst ((1)) () (2 3) ((4)))
    (fst () (1) () ((2 3) (4)))
    (fst () () (1) ((2 3) (4)))
    (final ((1) (2 3) (4)))))

(define (matcher-cut x k)
  (match x
    ((~append a (~cons (~cut! (~append b c)) d)) 
     (=> next back) (k `(fst ,a ,b ,c ,d)) (back))
    (x (k `(final ,x)))))

(test-restart matcher-cut
  '((1) (2 3) (4))
   ; commented-out solutions skipped because of cut!
   ; bt points inside (~append b c) are taken off
   ; the backtracking stack as soon as it produces
   ; its first solution
  '((fst ((1) (2 3)) (4) () ())
    ;(fst ((1) (2 3)) () (4) ())
    (fst ((1)) (2 3) () ((4)))
    ;(fst ((1)) (2) (3) ((4)))
    ;(fst ((1)) () (2 3) ((4)))
    (fst () (1) () ((2 3) (4)))
    ;(fst () () (1) ((2 3) (4)))
    (final ((1) (2 3) (4)))))


; custom matcher with (extended) lambda-list-like patterns

(display "\ncustom matcher-8\n")

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
  '((1                         number-one)
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
    (#(point 52 53 54 55)      (other #(point 52 53 54 55)))))


; avp's m5-compatible matcher
(display "\ncustom matcher-9\n")

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
(display "\ncustom matcher-9 test 1\n")
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
  '((1                          number-one)
    (a                          symbol-a)
    (((x y) q)                  (list (x y) q))
    (((a 2) (b a))              (head&tail a 2 b))
    ((+ 0 (+ y z) (+ y z))      (* 2 (+ y z)))
    ((+ (sin a b) (cos a b))    ((+ sin cos) a b))
    ((** 2 4)                   16)
    ((** 2 a)                   (generic (** 2 a)))
    ((123 456)                  (deconstructed (123 456) 123 456))))

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

(display "\nfaking limited or patterns\n")
(test-matcher m5-matcher-or
  '((1                   fourth)
    ((x x)               second)
    ((5 125)             squared)
    ((1 4)               squared)
    ((5 14)              third)
    ((,a)                quoted)
    ((,ab)               fourth)
    ((foo 13)            first)))


(display "\ncustom matcher-9 test 2\n")
(define (m5-matcher-2 x k)
  (m5-match x
    ((,@a ,(b symbol?) ,@c)  => (lambda (next) (k `(p1 ,a ,b ,c)) (next)))
    ((,@a ,@c ,x)            => (lambda (next) (k `(p2 ,a ,c ,x)) (next)))
    (,x                      (k `(p3 ,x)))))

(test-restart m5-matcher-2
  '(1 2 3 a 4 5)
  '((p1 (1 2 3) a (4 5))
    (p2 () (1 2 3 a 4) 5)
    (p3 (1 2 3 a 4 5))))

;; rollback to the next match
(display "\ncustom matcher-9 test 3\n")
(define (m5-matcher-3 x k)
  (m5-match x
    ((,@a ,(b symbol?) ,@c) ==> (lambda (next nr) (k `(fst ,a ,b ,c)) (next)))
    ((,@a ,@c)              ==> (lambda (next nr) (k `(snd ,a ,c)) (next)))
    (,x                     (k `(final ,x)))))

(test-restart m5-matcher-3
  '(1 x 3 y 5)
  '((fst (1) x (3 y 5))
    (fst (1 x 3) y (5))
    (snd () (1 x 3 y 5))
    (snd (1) (x 3 y 5))
    (snd (1 x) (3 y 5))
    (snd (1 x 3) (y 5))
    (snd (1 x 3 y) (5))
    (snd (1 x 3 y 5) ())
    (final (1 x 3 y 5))))


; syntax-rules -like matcher with standalone list of literal symbols
(display "\ncustom matcher-10\n")

(define-match-pattern ~srp->p (<...> <_>)
  ((_ l* ()) '())
  ((_ l* (x <...>)) (~etc (~srp->p l* x))) ; optimization
  ((_ l* (x <...> . y)) (~append/t y (~etc (~srp->p l* x)) (~srp->p l* y)))
  ((_ l* (x . y)) (~cons (~srp->p l* x) (~srp->p l* y)))
  ((_ l* #(x ...)) (~list->vector (~srp->p l* (x ...))))
  ((_ l* <_>) _)
  ((_ l* a) (~if-id-member a l* 'a a)))

(define-syntax sr-match
  (syntax-rules (=>)
    ((_ () l* v () (c ...))
     (match v c ... (_ (error "sr-match error" v))))
    ((_ () l* v ((srp . b) src ...) (c ...))
     (sr-match () l* v (src ...) (c ...
       ((~replace-specials <...> <_> (~srp->p l* srp)) . b))))
    ((_ x (l ...) src ...)
     (let ((v x)) (sr-match () (l ...) v (src ...) ())))))

(test-matcher
  (lambda (in)
    (sr-match in (a b)
      ((a x) 1)
      ((b x y) 2)
      ((a x y) 3)
      ((_ _ _) 4)))
  '(((a 17 37) 3)
    ((b 17 37) 2)
    ((c 17 37) 4)))

(test-matcher
  (lambda (in)
    (sr-match in (a)
      ((a x* ...) x*)))
  '(((a 17 37) (17 37))))

(test-matcher
  (lambda (in)
    (sr-match in (begin)
      ((begin (x* y*) ...) (list x* y*))))
  '(((begin (1 5) (2 6) (3 7) (4 8)) ((1 2 3 4) (5 6 7 8)))))

(test-matcher
  (lambda (in)
    (sr-match in ()
      (((x* y** ...) ...) (list x* y**))))
  '((((a b c d) (e f g) (h i) (j)) ((a e h j) ((b c d) (f g) (i) ())))))


; variant of SRFI-241/DFH catamorphism matcher
; (good enough to run SRFI-241 examples and tests)
(display "\ncustom matcher-11\n")

; Note: some R5RS systems may bail out here saying that -> is not a valid syntax for a symbol
; Pity, but that's what SRFI-241/DFH uses!

(define-match-pattern ~cmp->p (<...> <_> unquote ->)
  ((_ l ,(x)) (~prop l => x))
  ((_ l ,(f -> x ...)) (~prop f => x ...))
  ((_ l ,(x ...)) (~prop l => x ...))
  ((_ l ,<_>) _)
  ((_ l ,x) x)
  ((_ l ()) '())
  ((_ l (x <...>)) (~etc (~cmp->p l x))) ; optimization
  ((_ l (x <...> . y)) (~append/t y (~etc (~cmp->p l x)) (~cmp->p l y)))
  ((_ l (x . y)) (~cons (~cmp->p l x) (~cmp->p l y)))
  ((_ l #(x ...)) (~list->vector (~cmp->p l (x ...))))
  ((_ l other) 'other))

(define-syntax cm-match
  (syntax-rules (guard)
    ((_ () l x () (c ...))
     (match x c ... (_ (error "cm-match error" x))))
    ((_ () l x ((cmp (guard . e*) . b) cmc ...) (c ...))
     (cm-match () l x (cmc ...)
       (c ... ((~replace-specials <...> <_> (~cmp->p l cmp)) (=> n) (if (and . e*) (let () . b) (n))))))
    ((_ () l x ((cmp . b) cmc ...) (c ...))
     (cm-match () l x (cmc ...)
       (c ... ((~replace-specials <...> <_> (~cmp->p l cmp)) (let () . b)))))
    ((_ x cmc ...)
     (let l ((v x)) (cm-match () l v (cmc ...) ())))))

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x) 1)
      ((b ,x ,y) 2)
      ((a ,x ,y) 3)
      ((,_ ,_ ,_) 4)))
  '(((a 17 37) 3)
    ((b 17 37) 2)
    ((c 17 37) 4)))

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x) (- x))
      ((b ,x ,y) (+ x y))
      ((a ,x ,y) (* x y))))
  '(((a 17 37) 629)))

(test-matcher
  (lambda (in)
    (cm-match in
      ((a ,x* ...) x*)))
  '(((a 17 37) (17 37))))

(test-matcher
  (lambda (in)
    (cm-match in
      ((begin (,x* ,y*) ...) (append x* y*))))
  '(((begin (1 5) (2 6) (3 7) (4 8)) (1 2 3 4 5 6 7 8))))

(test-matcher
  (lambda (in)
    (cm-match in
      (((,x* ,y** ...) ...) (list x* y**))))
  '((((a b c d) (e f g) (h i) (j)) ((a e h j) ((b c d) (f g) (i) ())))))

(test-matcher
  (lambda (in)
    (letrec
      ((len (lambda (lst)
              (cm-match lst
                (() 0)
                ((,x ,x* ...) (+ 1 (len x*)))))))
      (len in)))
  '(((a b c d) 4)))

(test-matcher
  (lambda (in)
    (let ((len
           (lambda (lst)
             (cm-match lst
               (() 0)
               ((,x . ,(y)) (+ 1 y))))))
      (len in)))
  '(((a b c d) 4)))

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
  '(((a b c d e f) #((a c e) (b d f)))))

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
  '(((a b c d e f) #((a c e) (b d f)))))

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
  '(((+ (- 0 1) (+ 2 3)) 4)
    ((+ 1 2 3) 6)))

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
  '(((+ (- 0 1) (+ 2 3)) 4)))

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
  '(((program (set! x 3) (+ x 4)) (begin (set! x 3) (+ x 4)))))

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
  '(((program (let ((if (if x list values))) (if 1 2 3)))
     (begin (let ((if (if x list values))) (call if 1 2 3))))))

; test record matchers

(define-record-type <pare> (kons x y)
  pare? (x kar) (y kdr))

(define-record-match-pattern (~kons x y)
  pare? (y kdr) (x kar)) ; not order-sensitive!

(define-record-match-pattern (~v2 a b)
  (lambda (x) (and (vector? x) (= (vector-length x) 2)))
  (a (lambda (v) (vector-ref v 0)))
  (b (lambda (v) (vector-ref v 1))))

(define (matcher-rec x)
  (match x
    ((~kons x y)                      `(kons-of ,x ,y))
    ((~v2 a b)                        `(v2-of ,a ,b))
    (w                                `(other ,w))))

(display "\ntesting record patterns\n")
(test-matcher matcher-rec
  `((1 (other 1))
    ((1 . 4) (other (1 . 4)))
    (#(5 125) (v2-of 5 125))
    (,(kons 42 14) (kons-of 42 14))))

;(test '(other 1) (matcher-rec 1))
;(test '(other (1 . 4)) (matcher-rec '(1 . 4)))
;(test '(v2-of 5 125) (matcher-rec #(5 125)))
;(test '(kons-of 42 14) (matcher-rec (kons 42 14)))


; total balance
(cond ((zero? *errors*)
       (display "\nTotal: all tests passed!\n"))
      (else
       (display "\nTotal: ") (display *errors*)
       (display " tests failed!\n")))

