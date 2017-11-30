;; BEGIN HEADER

.class public test
.super java/lang/Object

.method public <init>()V
  .limit locals 1

  aload_0
  invokespecial java/lang/Object/<init>()V
  return

.end method

.method public static main([Ljava/lang/String;)V
  .limit locals 1
  .limit stack  1

  invokestatic test/main()I
  pop
  return

.end method

;; END HEADER

.method public static main()I
  .limit locals 1
  .limit stack  2

  ;; int x = 0;

  ldc 0
  istore 0

  ;; (void) printInt (++ x);

  iload 0
  ldc 1
  iadd
  istore 0
  iload 0
  invokestatic Runtime/printInt(I)V

  ;; return (int) x;

  iload 0
  ireturn

.end method
