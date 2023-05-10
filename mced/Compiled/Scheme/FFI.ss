(define SchemeFFI (lambda (_) 'FORALL))
(define pureScheme (lambda (_) (lambda (a) (lambda (_) a))))
(define bindScheme (lambda (_) (lambda (_) (lambda (a) (lambda (f) (lambda (ev) ((f (a ev)) ev)))))))
