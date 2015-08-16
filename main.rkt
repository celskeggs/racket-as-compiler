#lang racket

(require racket/stxparam)
(require racket/generic)

; utilities
(define (without-one entry list)
  (when (empty? list) (error "entry not in list: " entry list))
  (if (equal? (car list) entry)
      (cdr list)
      (cons list (without-one entry (cdr list)))))
(define (enumerate l)
  (map list (range 0 (length l)) l))

; types
(define-generics jtype
  [make-descriptor jtype])
(struct jprimitive-type (descriptor) #:inspector #f
  #:guard (lambda (descriptor _)
            (if (symbol? descriptor)
              descriptor
              (error "jprimitive-type descriptor must be a symbol!")))
  #:methods gen:jtype [(define (make-descriptor type)
                         (symbol->string (jprimitive-type-descriptor type)))])
(struct jarray (element) #:inspector #f
  #:guard (lambda (element _)
            (if (jtype? element)
              element
              (error "jarray element must be a type!")))
  #:methods gen:jtype [(define/generic make-descriptor-other make-descriptor)
                       (define (make-descriptor type)
                         (string-append "[" (make-descriptor-other (jarray-element type))))])
(struct jobject-type (class-name) #:inspector #f
  #:guard (lambda (class-name _)
            (if (symbol? class-name)
              class-name
              (error "jobject-type class-name must be a symbol!")))
  #:methods gen:jtype [(define (make-descriptor type)
                         (string-append "L" (symbol->string (jobject-type-class-name type)) ";"))])
(define jvoid (jprimitive-type 'V))
(define-syntax-rule (jobject name)
  (jobject-type 'name))

; base

(define-syntax-rule (pfmt data ...)
  (displayln (format data ...)))
(define-syntax-parameter jactive-class-name
  (lambda (stx)
    (raise-syntax-error #f "use of jactive-class-name outside of a class" stx)))
(define-syntax-parameter jactive-superclass-name
  (lambda (stx)
    (raise-syntax-error #f "use of jactive-superclass-name outside of a class" stx)))
(define-syntax-parameter jactive-method-ref
  (lambda (stx)
    (raise-syntax-error #f "use of jactive-method-ref outside of a method" stx)))

; method refs

(define (make-method-descriptor-relative ref)
  (format "~s(~a)~a"
          (jmethod-ref-type-method-name ref)
          (string-append* (map make-descriptor (jmethod-ref-type-argtypes ref)))
          (make-descriptor (jmethod-ref-type-rettype ref))))
(define (make-method-descriptor ref)
  (format "~s/~a"
          (jmethod-ref-type-class-name ref)
          (make-method-descriptor-relative ref)))
(struct jmethod-ref-type (class-name method-name argtypes rettype) #:inspector #f)
(define-syntax-rule (jmethod-ref class-name method-name argtype ... rettype)
  (jmethod-ref-type 'class-name 'method-name (list argtype ...) rettype))

; field refs

(struct jfield-ref-type (class-name field-name type) #:inspector #f)
(define-syntax-rule (jfield-ref class-name field-name type)
  (jfield-ref-type 'class-name 'field-name type))

; common

(define-syntax-rule (jbase-invoke #:invokename invokename #:method-ref method-ref arguments ...)
  (let* ((argument-residues (list arguments ...))
         (arguments-max-stack (apply max (cons 0
                                               (for/list ((residue argument-residues)
                                                          (previous-pushed-args (range 0 (length argument-residues))))
                                                 (+ (expression-residue-max-used-stack residue) previous-pushed-args))))))
      (pfmt "  ~s ~a" 'invokename (make-method-descriptor method-ref))
      (max (length argument-residues) arguments-max-stack)))

; expressions

(struct expression-residue (max-used-stack))
; ] max-used-stack is zero when only this is pushed: anything above that is the extra amount needed.

(define (jslot-ref n)
  (pfmt "  aload ~s" n)
  (expression-residue 0))
(define (jconst-string str)
  ; TODO: proper escaping
  (pfmt "  ldc ~s" str)
  (expression-residue 0))
(define (jstatic-get field)
  (pfmt "  getstatic ~s/~s ~a" (jfield-ref-type-class-name field) (jfield-ref-type-field-name field) (make-descriptor (jfield-ref-type-type field)))
  (expression-residue 0))

; statements

(struct statement-residue (max-used-stack))
(define (merge-statement-residues residues)
  (statement-residue
   (apply max (map statement-residue-max-used-stack residues))))

(define-syntax-rule (jinvokenonvirtual-void method-ref arguments ...)
  (begin
    (unless (equal? jvoid (jmethod-ref-type-rettype method-ref))
      (error "bad type to invokenonvirtual-void"))
    (statement-residue (jbase-invoke #:invokename invokenonvirtual #:method-ref method-ref
                                     arguments ...))))
(define-syntax-rule (jinvokenonvirtual-stmt method-ref arguments ...)
  (pop (jinvokenonvirtual-expr method-ref arguments ...)))
(define-syntax-rule (jinvokevirtual-void object method-ref arguments ...)
  (begin
    (unless (equal? jvoid (jmethod-ref-type-rettype method-ref))
      (error "bad type to invokevirtual-void"))
    (statement-residue (jbase-invoke #:invokename invokevirtual #:method-ref method-ref
                                     object arguments ...))))
(define-syntax-rule (jinvokevirtual-stmt method-ref arguments ...)
  (pop (jinvokevirtual-expr method-ref arguments ...)))
(define-syntax jreturn
  (syntax-rules (jreturn)
    ((jreturn)
     (begin
       (unless (equal? jvoid (jmethod-ref-type-rettype jactive-method-ref))
         (error "attempt to return nothing from a non-void method"))
       (pfmt "  return")
       (statement-residue 0)))
    ((jreturn value)
     (let ((arg-residue value))
       (eval-case (jmethod-ref-type-rettype jactive-method-ref)
                  [(jvoid)
                   (error "attempt to return something from a void method")]
                  ; TODO: actual types
                  ;(pfmt "  ?return")
                  ;(statement-residue (+ 1 (expression-residue-max-used-stack arg-residue)))
                  )))))

; source structures
(define (process-modifiers-without-access modifiers)
  (if (member 'static modifiers)
      (if (empty? (cdr modifiers))
          "static "
          (error "invalid modifiers: " (without-one 'static modifiers)))
      (if (empty? modifiers)
          ""
          (error "invalid modifiers: " modifiers))))
(define (process-modifiers modifiers)
  (cond ((member 'public modifiers)
         (error "public is not a valid modifier - it's default"))
        ((member 'private modifiers)
         (string-append "private " (process-modifiers-without-access (without-one 'private modifiers))))
        ((member 'package-private modifiers)
         (process-modifiers-without-access (without-one 'package-private modifiers)))
        ((member 'protected modifiers)
         (string-append "protected " (process-modifiers-without-access (without-one 'protected modifiers))))
        (else
         (string-append "public " (process-modifiers-without-access modifiers)))))
(define-syntax-rule (jclass name super contents ...)
  (let ((name-value 'name) (super-value 'super))
    (syntax-parameterize ([jactive-class-name (make-rename-transformer #'name-value)]
                          [jactive-superclass-name (make-rename-transformer #'super-value)])
                         (pfmt ".class public ~s" name-value)
                         (pfmt ".super ~s" super-value)
                         contents ...)))
(define-syntax-rule (jmethod (descriptor ...) name (type ...) rettype code ...)
  (let ((local-ref (jmethod-ref-type jactive-class-name 'name (list type ...) rettype)))
    (syntax-parameterize ([jactive-method-ref (make-rename-transformer #'local-ref)])
                         (pfmt ".method ~a ~a" (process-modifiers '(descriptor ...)) (make-method-descriptor-relative local-ref))
                         (let ((total-residue (merge-statement-residues (list
                                                                         code ...))))
                           (pfmt "  .limit stack ~s" (statement-residue-max-used-stack total-residue)))
                         (pfmt ".end method"))))
(define-syntax-rule (jmethod-void (descriptor ...) name (type ...) code ...)
  (jmethod (descriptor ...) name (type ...) jvoid
           code ...
           (jreturn)))
(define-syntax-rule (jinit (descriptor ...) (type ...) (superarg ...) code ...)
  (begin
    (jmethod-void (descriptor ...) <init> (type ...)
                  (jinvokenonvirtual-void (jmethod-ref-type jactive-superclass-name '<init>
                                                            (list (jtype-of superarg) ...) jvoid)
                                          (jslot-ref 0) superarg ...) ; TODO: use jthis
                  code ...)))

; source macros

(define-syntax-rule (Jclass-base name contents ...)
  (jclass name java/lang/Object contents ...))
(define-syntax-rule (Jmain code ...)
  (jmethod-void (static) main ((jarray (jobject java/lang/String)))
                code ...))
(define-syntax-rule (Jinvokevirtual object (class-name method-name args ... rettype) arguments ...)
  (jinvokevirtual object (jmethod-ref class-name method-name args ... rettype) arguments ...))
(define-syntax-rule (Jinvokevirtual-void object (class-name method-name args ...) arguments ...)
  (jinvokevirtual-void object (jmethod-ref class-name method-name args ... jvoid) arguments ...))

; example

(Jclass-base HelloWorld
             (Jmain (Jinvokevirtual-void (jstatic-get (jfield-ref java/lang/System out (jobject java/io/PrintStream)))
                                         (java/io/PrintStream println (jobject java/lang/String))
                                         (jconst-string "Hello, World!"))))