# Vmp3_64bit_disasm-prerelease- WIP WIP WIP
Some handlers are not supported, I cannot be asked to implement all the obscure ones lmao
## Info

This project was tested on vgk.sys (sha-1 266ddd98fdd9df939993d947b0edb052a347316f)

## Example

### Call into vmp3 with pushed value
![example1](https://user-images.githubusercontent.com/102005914/175548145-8cb85a51-fef4-4a4c-b11b-f8049636b590.png)

### Converting the address to decimal ( Newest commit fixed this use hex addresses now )
![example2](https://user-images.githubusercontent.com/102005914/175548162-5d352eda-c66c-481b-ac7a-1697faa23e09.png)

### Invoking the disassembler
![example3](https://user-images.githubusercontent.com/102005914/175548166-ccc3bde9-fd20-44b7-850e-5b2c07119874.png)

## Example Output
```
0x14039cf4b     | pop64 r19                      | 0x140725d72
0x14039cf50     | pop64 r10                      | 0x14069504f
0x14039cf55     | pop64 r9                       | 0x1406d0453
0x14039cf5a     | pop64 r18                      | 0x14069a8da
0x14039cf5f     | pop64 r11                      | 0x1406de987
0x14039cf64     | pop64 r22                      | 0x140740966
0x14039cf69     | pop64 r21                      | 0x14076a534
0x14039cf6e     | pop64 r8                       | 0x14073cc29
0x14039cf73     | pop64 r17                      | 0x14066b565
0x14039cf78     | pop64 r7                       | 0x1406c5fd7
0x14039cf7d     | pop64 r5                       | 0x1406a0a37
0x14039cf82     | pop64 r0                       | 0x140725d72
0x14039cf87     | pop64 r16                      | 0x14069504f
0x14039cf8c     | pop64 r4                       | 0x1406d0453
0x14039cf91     | pop64 r13                      | 0x14069a8da
0x14039cf96     | pop64 r3                       | 0x1406de987
0x14039cf9b     | pop64 r2                       | 0x140740966
0x14039cfa0     | pop64 r14                      | 0x14076a534
0x14039cfa5     | pop64 r15                      | 0x14073cc29
0x14039cfaa     | push_imm64 0x1400148a2         | 0x1406b58aa
0x14039cfb6     | push64 r19                     | 0x1407233bb
0x14039cfbb     | add64                          | 0x14065c9e4
0x14039cfbf     | pop64 r23                      | 0x14066b565
0x14039cfc4     | pop64 r24                      | 0x1406c5fd7
0x14039cfc9     | pushvsp64                      | 0x1406dd647
0x14039cfcd     | pop64 r25                      | 0x1406a0a37
0x14039cfd2     | push64 r3                      | 0x1407504ba
0x14039cfd7     | pop64 r26                      | 0x140725d72
0x14039cfdc     | push64 r2                      | 0x1406b0c5d
0x14039cfe1     | pop64 r27                      | 0x14069504f
0x14039cfe6     | push64 r13                     | 0x14073ce7e
0x14039cfeb     | pop64 r28                      | 0x1406d0453
0x14039cff0     | push64 r18                     | 0x140776f28
0x14039cff5     | pop64 r29                      | 0x14069a8da
0x14039cffa     | push_imm64 0x1407962a0         | 0x14066ecc1
0x14039d006     | push_imm32 0x3                 | 0x14068f1ea
0x14039d00e     | pop32 r16_dword_0              | 0x14067b681
0x14039d013     | push_imm32 0x0                 | 0x140756802
0x14039d01b     | pop32 r16_dword_1              | 0x14068d4fe
0x14039d020     | push_imm64 0x140074b10         | 0x140720d16
0x14039d02c     | push64 r19                     | 0x140652822
0x14039d031     | add64                          | 0x1406f2971
0x14039d035     | push64 r18                     | 0x140720c6d
0x14039d03a     | pop64 r23                      | 0x1406de987
0x14039d03f     | pop64 r20                      | 0x140740966
0x14039d044     | pop64 r12                      | 0x14076a534
0x14039d049     | push64 r19                     | 0x1407612e8
0x14039d04e     | add64                          | 0x140723579
0x14039d052     | pop64 r15                      | 0x14073cc29
0x14039d057     | push_imm64 0x140069068         | 0x140735929
0x14039d063     | push64 r19                     | 0x1406953ee
0x14039d068     | add64                          | 0x14071e780
0x14039d06c     | pop64 r11                      | 0x14066b565
0x14039d071     | fetch64                        | 0x14071bcc3
0x14039d075     | push64 r2                      | 0x140676a3e
0x14039d07a     | push64 r3                      | 0x140740fae
0x14039d07f     | push64 r13                     | 0x1407233bb
0x14039d084     | push64 r23                     | 0x1407504ba
0x14039d089     | push64 r16                     | 0x1406b0c5d
0x14039d08e     | push64 r0                      | 0x14073ce7e
0x14039d093     | push64 r5                      | 0x140776f28
0x14039d098     | push64 r7                      | 0x140652822
0x14039d09d     | push64 r17                     | 0x140720c6d
0x14039d0a2     | push64 r8                      | 0x1407612e8
0x14039d0a7     | push64 r21                     | 0x1406953ee
0x14039d0ac     | push64 r22                     | 0x140676a3e
0x14039d0b1     | push64 r12                     | 0x140740fae
0x14039d0b6     | push64 r18                     | 0x1407233bb
0x14039d0bb     | push64 r9                      | 0x1407504ba
0x14039d0c0     | push64 r10                     | 0x1406b0c5d
0x14039d0c5     | vm_exit                        | 0x1406f0494
Getting helper stub -> helperstub_14039cf47

define i64 @helperfunction_14039cf47(i64* noalias %rax, i64* noalias %rbx, i64* noalias %rcx, i64* noalias %rdx, i64* noalias %rsi, i64* noalias %rdi, i64* noalias %rbp, i64* noalias %rsp, i64* noalias %r8, i64* noalias %r9, i64* noalias %r10, i64* noalias %r11, i64* noalias %r12, i64* noalias %r13, i64* noalias %r14, i64* noalias %r15, i64* noalias %flags, i64 %KEY_STUB, i64 %RET_ADDR, i64 %REL_ADDR) {
  call void @llvm.experimental.noalias.scope.decl(metadata !10)
  call void @llvm.experimental.noalias.scope.decl(metadata !13)
  call void @llvm.experimental.noalias.scope.decl(metadata !15)
  call void @llvm.experimental.noalias.scope.decl(metadata !17)
  call void @llvm.experimental.noalias.scope.decl(metadata !19)
  %1 = load i64, i64* %rsp, align 8, !tbaa !3, !alias.scope !19, !noalias !21
  %2 = add i64 %1, -8
  %3 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %4 = bitcast i8* %3 to i64*
  %5 = load i64, i64* %rbx, align 8, !alias.scope !10, !noalias !36
  store i64 5376664224, i64* %4, align 1, !noalias !37
  %6 = load i64, i64* bitcast (i8* getelementptr inbounds ([0 x i8], [0 x i8]* @RAM, i64 0, i64 5369139304) to i64*), align 1, !noalias !37
  store i64 5369187088, i64* %r8, align 8, !tbaa !3, !alias.scope !17, !noalias !38
  store i64 3, i64* %rcx, align 8, !tbaa !3, !alias.scope !13, !noalias !39
  store i64 %5, i64* %rdx, align 8, !tbaa !3, !alias.scope !15, !noalias !40
  store i64 %2, i64* %rsp, align 8, !tbaa !3, !alias.scope !19, !noalias !21
  ret i64 %6
}

```

# Open source software usage
The c++ code that compiles to the llvm helper file was released by FvrMateo and is available here https://github.com/LLVMParty/TicklingVMProtect/tree/master/Helpers


This project uses the following open source rust crates
- iced_x86 https://github.com/icedland/iced
- clap https://github.com/icedland/iced
- pelite https://github.com/CasualX/pelite
- haybale https://github.com/PLSysSec/haybale
- inkwell https://github.com/TheDan64/inkwell
- petgraph https://github.com/petgraph/petgraph

The project also makes heavy use of llvm software

