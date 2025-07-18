(define caar (lambda (pair) (car (car pair))))

(define cadr (lambda (pair) (car (cdr pair))))
(define cdar (lambda (pair) (cdr (car pair))))
(define cddr (lambda (pair) (cdr (cdr pair))))

(define wahoo (lambda (x) (x + x)))

(define adult? (lambda (age)
  (if (>= age 18)
    "adult"
    "minor")))

(display (show (adult? 10)))

; (cdr (quote (1 2 {-teeest-} 5 4 6 "waaa")))
