_start:
    mov x0, #1          // file descriptor (stdout)
    ldr x1, =msg        // pointer to message
    mov x2, #14         // message length
    mov x8, #64         // syscall number for write
    svc #0              // make syscall

    mov x8, #93         // syscall number for exit
    mov x0, #0          // exit code
    svc #0              // make syscall
msg:    .asciz "hello, world!\n"
