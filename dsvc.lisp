(defun known (a lst)
   (if lst
       (push a (known a (cdr lst)))
       nil))