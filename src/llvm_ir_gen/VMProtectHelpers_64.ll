; ModuleID = 'VMProtectHelpers.cpp'
source_filename = "VMProtectHelpers.cpp"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.VirtualRegister = type { %union.anon }
%union.anon = type { i64 }
%struct.anon = type { i8, i8, i8, i8, i8, i8, i8, i8 }
%struct.VirtualContext = type { %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister, %struct.VirtualRegister }

$_Z8PUSH_IMMImEvRmT_ = comdat any

$_Z8PUSH_IMMIjEvRmT_ = comdat any

$_Z8PUSH_IMMItEvRmT_ = comdat any

$_Z8PUSH_VSPILm64EEvRm = comdat any

$_Z8PUSH_VSPILm32EEvRm = comdat any

$_Z8PUSH_VSPILm16EEvRm = comdat any

$_Z7POP_VSPILm64EEvRm = comdat any

$_Z7POP_VSPILm32EEvRm = comdat any

$_Z7POP_VSPILm16EEvRm = comdat any

$_Z4LOADImEvRm = comdat any

$_Z4LOADIjEvRm = comdat any

$_Z4LOADItEvRm = comdat any

$_Z4LOADIhEvRm = comdat any

$_Z7LOAD_GSImEvRm = comdat any

$_Z7LOAD_GSIjEvRm = comdat any

$_Z7LOAD_GSItEvRm = comdat any

$_Z7LOAD_GSIhEvRm = comdat any

$_Z7LOAD_FSImEvRm = comdat any

$_Z7LOAD_FSIjEvRm = comdat any

$_Z7LOAD_FSItEvRm = comdat any

$_Z7LOAD_FSIhEvRm = comdat any

$_Z5STOREImEvRm = comdat any

$_Z5STOREIjEvRm = comdat any

$_Z5STOREItEvRm = comdat any

$_Z5STOREIhEvRm = comdat any

$_Z10PUSH_VMREGILm8ELm0EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm8ELm1EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm16ELm0EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm16ELm1EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm16ELm2EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm16ELm3EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm32ELm0EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm32ELm1EEvRm15VirtualRegister = comdat any

$_Z10PUSH_VMREGILm64ELm0EEvRm15VirtualRegister = comdat any

$_Z9POP_VMREGILm8ELm0EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm8ELm1EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm16ELm0EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm16ELm1EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm16ELm2EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm16ELm3EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm32ELm0EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm32ELm1EEvRmR15VirtualRegister = comdat any

$_Z9POP_VMREGILm64ELm0EEvRmR15VirtualRegister = comdat any

$_Z3ADDImEvRm = comdat any

$_Z3ADDIjEvRm = comdat any

$_Z3ADDItEvRm = comdat any

$_Z3ADDIhEvRm = comdat any

$_Z3DIVImEvRm = comdat any

$_Z3DIVIjEvRm = comdat any

$_Z3DIVItEvRm = comdat any

$_Z3DIVIhEvRm = comdat any

$_Z4IDIVImEvRm = comdat any

$_Z4IDIVIjEvRm = comdat any

$_Z4IDIVItEvRm = comdat any

$_Z4IDIVIhEvRm = comdat any

$_Z3MULImEvRm = comdat any

$_Z3MULIjEvRm = comdat any

$_Z3MULItEvRm = comdat any

$_Z3MULIhEvRm = comdat any

$_Z4IMULImEvRm = comdat any

$_Z4IMULIjEvRm = comdat any

$_Z4IMULItEvRm = comdat any

$_Z4IMULIhEvRm = comdat any

$_Z3NORImEvRm = comdat any

$_Z3NORIjEvRm = comdat any

$_Z3NORItEvRm = comdat any

$_Z3NORIhEvRm = comdat any

$_Z4NANDImEvRm = comdat any

$_Z4NANDIjEvRm = comdat any

$_Z4NANDItEvRm = comdat any

$_Z4NANDIhEvRm = comdat any

$_Z3SHLImEvRm = comdat any

$_Z3SHLIjEvRm = comdat any

$_Z3SHLItEvRm = comdat any

$_Z3SHLIhEvRm = comdat any

$_Z3SHRImEvRm = comdat any

$_Z3SHRIjEvRm = comdat any

$_Z3SHRItEvRm = comdat any

$_Z3SHRIhEvRm = comdat any

$_Z4SHLDImEvRm = comdat any

$_Z4SHLDIjEvRm = comdat any

$_Z4SHLDItEvRm = comdat any

$_Z4SHLDIhEvRm = comdat any

$_Z4SHRDImEvRm = comdat any

$_Z4SHRDIjEvRm = comdat any

$_Z4SHRDItEvRm = comdat any

$_Z4SHRDIhEvRm = comdat any

@SEM_PUSH_CR0 = dso_local constant void (i64*)* @_Z8PUSH_CR0Rm, align 8
@SEM_PUSH_IMM_64 = dso_local constant void (i64*, i64)* @_Z8PUSH_IMMImEvRmT_, align 8
@SEM_PUSH_IMM_32 = dso_local constant void (i64*, i32)* @_Z8PUSH_IMMIjEvRmT_, align 8
@SEM_PUSH_IMM_16 = dso_local constant void (i64*, i16)* @_Z8PUSH_IMMItEvRmT_, align 8
@SEM_PUSH_VSP_64 = dso_local constant void (i64*)* @_Z8PUSH_VSPILm64EEvRm, align 8
@SEM_PUSH_VSP_32 = dso_local constant void (i64*)* @_Z8PUSH_VSPILm32EEvRm, align 8
@SEM_PUSH_VSP_16 = dso_local constant void (i64*)* @_Z8PUSH_VSPILm16EEvRm, align 8
@SEM_POP_VSP_64 = dso_local constant void (i64*)* @_Z7POP_VSPILm64EEvRm, align 8
@SEM_POP_VSP_32 = dso_local constant void (i64*)* @_Z7POP_VSPILm32EEvRm, align 8
@SEM_POP_VSP_16 = dso_local constant void (i64*)* @_Z7POP_VSPILm16EEvRm, align 8
@SEM_POP_FLAGS = dso_local constant void (i64*, i64*)* @_Z9POP_FLAGSRmS_, align 8
@SEM_LOAD_SS_64 = dso_local constant void (i64*)* @_Z4LOADImEvRm, align 8
@SEM_LOAD_SS_32 = dso_local constant void (i64*)* @_Z4LOADIjEvRm, align 8
@SEM_LOAD_SS_16 = dso_local constant void (i64*)* @_Z4LOADItEvRm, align 8
@SEM_LOAD_SS_8 = dso_local constant void (i64*)* @_Z4LOADIhEvRm, align 8
@SEM_LOAD_DS_64 = dso_local constant void (i64*)* @_Z4LOADImEvRm, align 8
@SEM_LOAD_DS_32 = dso_local constant void (i64*)* @_Z4LOADIjEvRm, align 8
@SEM_LOAD_DS_16 = dso_local constant void (i64*)* @_Z4LOADItEvRm, align 8
@SEM_LOAD_DS_8 = dso_local constant void (i64*)* @_Z4LOADIhEvRm, align 8
@SEM_LOAD_GS_64 = dso_local constant void (i64*)* @_Z7LOAD_GSImEvRm, align 8
@SEM_LOAD_GS_32 = dso_local constant void (i64*)* @_Z7LOAD_GSIjEvRm, align 8
@SEM_LOAD_GS_16 = dso_local constant void (i64*)* @_Z7LOAD_GSItEvRm, align 8
@SEM_LOAD_GS_8 = dso_local constant void (i64*)* @_Z7LOAD_GSIhEvRm, align 8
@SEM_LOAD_FS_64 = dso_local constant void (i64*)* @_Z7LOAD_FSImEvRm, align 8
@SEM_LOAD_FS_32 = dso_local constant void (i64*)* @_Z7LOAD_FSIjEvRm, align 8
@SEM_LOAD_FS_16 = dso_local constant void (i64*)* @_Z7LOAD_FSItEvRm, align 8
@SEM_LOAD_FS_8 = dso_local constant void (i64*)* @_Z7LOAD_FSIhEvRm, align 8
@SEM_STORE_SS_64 = dso_local constant void (i64*)* @_Z5STOREImEvRm, align 8
@SEM_STORE_SS_32 = dso_local constant void (i64*)* @_Z5STOREIjEvRm, align 8
@SEM_STORE_SS_16 = dso_local constant void (i64*)* @_Z5STOREItEvRm, align 8
@SEM_STORE_SS_8 = dso_local constant void (i64*)* @_Z5STOREIhEvRm, align 8
@SEM_STORE_DS_64 = dso_local constant void (i64*)* @_Z5STOREImEvRm, align 8
@SEM_STORE_DS_32 = dso_local constant void (i64*)* @_Z5STOREIjEvRm, align 8
@SEM_STORE_DS_16 = dso_local constant void (i64*)* @_Z5STOREItEvRm, align 8
@SEM_STORE_DS_8 = dso_local constant void (i64*)* @_Z5STOREIhEvRm, align 8
@SEM_PUSH_VMREG_8_LOW = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm8ELm0EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_8_HIGH = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm8ELm1EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_16_LOWLOW = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm16ELm0EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_16_LOWHIGH = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm16ELm1EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_16_HIGHLOW = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm16ELm2EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_16_HIGHHIGH = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm16ELm3EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_32_LOW = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm32ELm0EEvRm15VirtualRegister, align 8
@SEM_UNDEF_PUSH_VMREG_32 = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm32ELm0EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_32_HIGH = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm32ELm1EEvRm15VirtualRegister, align 8
@SEM_PUSH_VMREG_64 = dso_local constant void (i64*, i64)* @_Z10PUSH_VMREGILm64ELm0EEvRm15VirtualRegister, align 8
@SEM_POP_VMREG_8_LOW = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm8ELm0EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_8_HIGH = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm8ELm1EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_16_LOWLOW = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm16ELm0EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_16_LOWHIGH = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm16ELm1EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_16_HIGHLOW = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm16ELm2EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_16_HIGHHIGH = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm16ELm3EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_32_LOW = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm32ELm0EEvRmR15VirtualRegister, align 8
@SEM_UNDEF_POP_VMREG_32 = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm32ELm0EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_32_HIGH = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm32ELm1EEvRmR15VirtualRegister, align 8
@SEM_POP_VMREG_64 = dso_local constant void (i64*, %struct.VirtualRegister*)* @_Z9POP_VMREGILm64ELm0EEvRmR15VirtualRegister, align 8
@SEM_PUSH_REG_64 = dso_local constant void (i64*, i64)* @_Z8PUSH_REGRmm, align 8
@SEM_UNDEF_PUSH_REG_32 = dso_local constant void (i64*, i64)* @_Z8PUSH_REGRmm, align 8
@SEM_POP_REG_64 = dso_local constant void (i64*, i64*)* @_Z7POP_REGRmS_, align 8
@SEM_UNDEF_POP_REG_32 = dso_local constant void (i64*, i64*)* @_Z7POP_REGRmS_, align 8
@SEM_POP_VOID_64 = dso_local constant void (i64*)* @_Z8POP_VOIDRm, align 8
@SEM_UNDEF_POP_VOID_32 = dso_local constant void (i64*)* @_Z8POP_VOIDRm, align 8
@SEM_MOVE_VMREG_SLOT = dso_local constant void (%struct.VirtualRegister*, i64*)* @_Z15MOVE_VMREG_SLOTR15VirtualRegisterRm, align 8
@SEM_UNDEF_MOVE_VMREG_SLOT = dso_local constant void (%struct.VirtualRegister*, i64*)* @_Z15MOVE_VMREG_SLOTR15VirtualRegisterRm, align 8
@SEM_POP_SLOT = dso_local constant void (i64*, i64*)* @_Z8POP_SLOTRmS_, align 8
@SEM_UNDEF_POP_SLOT = dso_local constant void (i64*, i64*)* @_Z8POP_SLOTRmS_, align 8
@SEM_CPUID = dso_local constant void (i64*)* @_Z5CPUIDRm, align 8
@SEM_RDTSC = dso_local constant void (i64*)* @_Z5RDTSCRm, align 8
@SEM_ADD_64 = dso_local constant void (i64*)* @_Z3ADDImEvRm, align 8
@SEM_ADD_32 = dso_local constant void (i64*)* @_Z3ADDIjEvRm, align 8
@SEM_ADD_16 = dso_local constant void (i64*)* @_Z3ADDItEvRm, align 8
@SEM_ADD_8 = dso_local constant void (i64*)* @_Z3ADDIhEvRm, align 8
@SEM_DIV_64 = dso_local constant void (i64*)* @_Z3DIVImEvRm, align 8
@SEM_DIV_32 = dso_local constant void (i64*)* @_Z3DIVIjEvRm, align 8
@SEM_DIV_16 = dso_local constant void (i64*)* @_Z3DIVItEvRm, align 8
@SEM_DIV_8 = dso_local constant void (i64*)* @_Z3DIVIhEvRm, align 8
@SEM_IDIV_64 = dso_local constant void (i64*)* @_Z4IDIVImEvRm, align 8
@SEM_IDIV_32 = dso_local constant void (i64*)* @_Z4IDIVIjEvRm, align 8
@SEM_IDIV_16 = dso_local constant void (i64*)* @_Z4IDIVItEvRm, align 8
@SEM_IDIV_8 = dso_local constant void (i64*)* @_Z4IDIVIhEvRm, align 8
@SEM_MUL_64 = dso_local constant void (i64*)* @_Z3MULImEvRm, align 8
@SEM_MUL_32 = dso_local constant void (i64*)* @_Z3MULIjEvRm, align 8
@SEM_MUL_16 = dso_local constant void (i64*)* @_Z3MULItEvRm, align 8
@SEM_MUL_8 = dso_local constant void (i64*)* @_Z3MULIhEvRm, align 8
@SEM_IMUL_64 = dso_local constant void (i64*)* @_Z4IMULImEvRm, align 8
@SEM_IMUL_32 = dso_local constant void (i64*)* @_Z4IMULIjEvRm, align 8
@SEM_IMUL_16 = dso_local constant void (i64*)* @_Z4IMULItEvRm, align 8
@SEM_IMUL_8 = dso_local constant void (i64*)* @_Z4IMULIhEvRm, align 8
@SEM_NOR_64 = dso_local constant void (i64*)* @_Z3NORImEvRm, align 8
@SEM_NOR_32 = dso_local constant void (i64*)* @_Z3NORIjEvRm, align 8
@SEM_NOR_16 = dso_local constant void (i64*)* @_Z3NORItEvRm, align 8
@SEM_NOR_8 = dso_local constant void (i64*)* @_Z3NORIhEvRm, align 8
@SEM_NAND_64 = dso_local constant void (i64*)* @_Z4NANDImEvRm, align 8
@SEM_NAND_32 = dso_local constant void (i64*)* @_Z4NANDIjEvRm, align 8
@SEM_NAND_16 = dso_local constant void (i64*)* @_Z4NANDItEvRm, align 8
@SEM_NAND_8 = dso_local constant void (i64*)* @_Z4NANDIhEvRm, align 8
@SEM_SHL_64 = dso_local constant void (i64*)* @_Z3SHLImEvRm, align 8
@SEM_SHL_32 = dso_local constant void (i64*)* @_Z3SHLIjEvRm, align 8
@SEM_SHL_16 = dso_local constant void (i64*)* @_Z3SHLItEvRm, align 8
@SEM_SHL_8 = dso_local constant void (i64*)* @_Z3SHLIhEvRm, align 8
@SEM_SHR_64 = dso_local constant void (i64*)* @_Z3SHRImEvRm, align 8
@SEM_SHR_32 = dso_local constant void (i64*)* @_Z3SHRIjEvRm, align 8
@SEM_SHR_16 = dso_local constant void (i64*)* @_Z3SHRItEvRm, align 8
@SEM_SHR_8 = dso_local constant void (i64*)* @_Z3SHRIhEvRm, align 8
@SEM_SHLD_64 = dso_local constant void (i64*)* @_Z4SHLDImEvRm, align 8
@SEM_SHLD_32 = dso_local constant void (i64*)* @_Z4SHLDIjEvRm, align 8
@SEM_SHLD_16 = dso_local constant void (i64*)* @_Z4SHLDItEvRm, align 8
@SEM_SHLD_8 = dso_local constant void (i64*)* @_Z4SHLDIhEvRm, align 8
@SEM_SHRD_64 = dso_local constant void (i64*)* @_Z4SHRDImEvRm, align 8
@SEM_SHRD_32 = dso_local constant void (i64*)* @_Z4SHRDIjEvRm, align 8
@SEM_SHRD_16 = dso_local constant void (i64*)* @_Z4SHRDItEvRm, align 8
@SEM_SHRD_8 = dso_local constant void (i64*)* @_Z4SHRDIhEvRm, align 8
@SEM_JUMP_INC = dso_local constant void (i64*, i64*)* @_Z8JUMP_INCRmS_, align 8
@SEM_JUMP_DEC = dso_local constant void (i64*, i64*)* @_Z8JUMP_DECRmS_, align 8
@SEM_JUMP = dso_local constant void (i64*, i64*)* @_Z4JUMPRmS_, align 8
@SEM_EXIT = dso_local constant void (i64*, i64*)* @_Z4JUMPRmS_, align 8
@RAM = external dso_local local_unnamed_addr global [0 x i8], align 1
@GS = external dso_local local_unnamed_addr global [0 x i8], align 1
@FS = external dso_local local_unnamed_addr global [0 x i8], align 1
@__undef = external dso_local local_unnamed_addr global i64, align 8
@llvm.compiler.used = appending global [115 x i8*] [i8* bitcast (void (i64*)** @SEM_ADD_16 to i8*), i8* bitcast (void (i64*)** @SEM_ADD_32 to i8*), i8* bitcast (void (i64*)** @SEM_ADD_64 to i8*), i8* bitcast (void (i64*)** @SEM_ADD_8 to i8*), i8* bitcast (void (i64*)** @SEM_CPUID to i8*), i8* bitcast (void (i64*)** @SEM_DIV_16 to i8*), i8* bitcast (void (i64*)** @SEM_DIV_32 to i8*), i8* bitcast (void (i64*)** @SEM_DIV_64 to i8*), i8* bitcast (void (i64*)** @SEM_DIV_8 to i8*), i8* bitcast (void (i64*, i64*)** @SEM_EXIT to i8*), i8* bitcast (void (i64*)** @SEM_IDIV_16 to i8*), i8* bitcast (void (i64*)** @SEM_IDIV_32 to i8*), i8* bitcast (void (i64*)** @SEM_IDIV_64 to i8*), i8* bitcast (void (i64*)** @SEM_IDIV_8 to i8*), i8* bitcast (void (i64*)** @SEM_IMUL_16 to i8*), i8* bitcast (void (i64*)** @SEM_IMUL_32 to i8*), i8* bitcast (void (i64*)** @SEM_IMUL_64 to i8*), i8* bitcast (void (i64*)** @SEM_IMUL_8 to i8*), i8* bitcast (void (i64*, i64*)** @SEM_JUMP to i8*), i8* bitcast (void (i64*, i64*)** @SEM_JUMP_DEC to i8*), i8* bitcast (void (i64*, i64*)** @SEM_JUMP_INC to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_DS_16 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_DS_32 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_DS_64 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_DS_8 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_FS_16 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_FS_32 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_FS_64 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_FS_8 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_GS_16 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_GS_32 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_GS_64 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_GS_8 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_SS_16 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_SS_32 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_SS_64 to i8*), i8* bitcast (void (i64*)** @SEM_LOAD_SS_8 to i8*), i8* bitcast (void (%struct.VirtualRegister*, i64*)** @SEM_MOVE_VMREG_SLOT to i8*), i8* bitcast (void (i64*)** @SEM_MUL_16 to i8*), i8* bitcast (void (i64*)** @SEM_MUL_32 to i8*), i8* bitcast (void (i64*)** @SEM_MUL_64 to i8*), i8* bitcast (void (i64*)** @SEM_MUL_8 to i8*), i8* bitcast (void (i64*)** @SEM_NAND_16 to i8*), i8* bitcast (void (i64*)** @SEM_NAND_32 to i8*), i8* bitcast (void (i64*)** @SEM_NAND_64 to i8*), i8* bitcast (void (i64*)** @SEM_NAND_8 to i8*), i8* bitcast (void (i64*)** @SEM_NOR_16 to i8*), i8* bitcast (void (i64*)** @SEM_NOR_32 to i8*), i8* bitcast (void (i64*)** @SEM_NOR_64 to i8*), i8* bitcast (void (i64*)** @SEM_NOR_8 to i8*), i8* bitcast (void (i64*, i64*)** @SEM_POP_FLAGS to i8*), i8* bitcast (void (i64*, i64*)** @SEM_POP_REG_64 to i8*), i8* bitcast (void (i64*, i64*)** @SEM_POP_SLOT to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_16_HIGHHIGH to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_16_HIGHLOW to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_16_LOWHIGH to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_16_LOWLOW to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_32_HIGH to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_32_LOW to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_64 to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_8_HIGH to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_POP_VMREG_8_LOW to i8*), i8* bitcast (void (i64*)** @SEM_POP_VOID_64 to i8*), i8* bitcast (void (i64*)** @SEM_POP_VSP_16 to i8*), i8* bitcast (void (i64*)** @SEM_POP_VSP_32 to i8*), i8* bitcast (void (i64*)** @SEM_POP_VSP_64 to i8*), i8* bitcast (void (i64*)** @SEM_PUSH_CR0 to i8*), i8* bitcast (void (i64*, i16)** @SEM_PUSH_IMM_16 to i8*), i8* bitcast (void (i64*, i32)** @SEM_PUSH_IMM_32 to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_IMM_64 to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_REG_64 to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_16_HIGHHIGH to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_16_HIGHLOW to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_16_LOWHIGH to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_16_LOWLOW to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_32_HIGH to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_32_LOW to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_64 to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_8_HIGH to i8*), i8* bitcast (void (i64*, i64)** @SEM_PUSH_VMREG_8_LOW to i8*), i8* bitcast (void (i64*)** @SEM_PUSH_VSP_16 to i8*), i8* bitcast (void (i64*)** @SEM_PUSH_VSP_32 to i8*), i8* bitcast (void (i64*)** @SEM_PUSH_VSP_64 to i8*), i8* bitcast (void (i64*)** @SEM_RDTSC to i8*), i8* bitcast (void (i64*)** @SEM_SHLD_16 to i8*), i8* bitcast (void (i64*)** @SEM_SHLD_32 to i8*), i8* bitcast (void (i64*)** @SEM_SHLD_64 to i8*), i8* bitcast (void (i64*)** @SEM_SHLD_8 to i8*), i8* bitcast (void (i64*)** @SEM_SHL_16 to i8*), i8* bitcast (void (i64*)** @SEM_SHL_32 to i8*), i8* bitcast (void (i64*)** @SEM_SHL_64 to i8*), i8* bitcast (void (i64*)** @SEM_SHL_8 to i8*), i8* bitcast (void (i64*)** @SEM_SHRD_16 to i8*), i8* bitcast (void (i64*)** @SEM_SHRD_32 to i8*), i8* bitcast (void (i64*)** @SEM_SHRD_64 to i8*), i8* bitcast (void (i64*)** @SEM_SHRD_8 to i8*), i8* bitcast (void (i64*)** @SEM_SHR_16 to i8*), i8* bitcast (void (i64*)** @SEM_SHR_32 to i8*), i8* bitcast (void (i64*)** @SEM_SHR_64 to i8*), i8* bitcast (void (i64*)** @SEM_SHR_8 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_DS_16 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_DS_32 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_DS_64 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_DS_8 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_SS_16 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_SS_32 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_SS_64 to i8*), i8* bitcast (void (i64*)** @SEM_STORE_SS_8 to i8*), i8* bitcast (void (%struct.VirtualRegister*, i64*)** @SEM_UNDEF_MOVE_VMREG_SLOT to i8*), i8* bitcast (void (i64*, i64*)** @SEM_UNDEF_POP_REG_32 to i8*), i8* bitcast (void (i64*, i64*)** @SEM_UNDEF_POP_SLOT to i8*), i8* bitcast (void (i64*, %struct.VirtualRegister*)** @SEM_UNDEF_POP_VMREG_32 to i8*), i8* bitcast (void (i64*)** @SEM_UNDEF_POP_VOID_32 to i8*), i8* bitcast (void (i64*, i64)** @SEM_UNDEF_PUSH_REG_32 to i8*), i8* bitcast (void (i64*, i64)** @SEM_UNDEF_PUSH_VMREG_32 to i8*)], section "llvm.metadata"

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define dso_local void @_Z8PUSH_CR0Rm(i64* nocapture nonnull align 8 dereferenceable(8) %vsp) #0 {
entry:
  %0 = tail call i64 asm "mov %cr0, $0", "=r,~{dirflag},~{fpsr},~{flags}"() #11, !srcloc !3
  %1 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %1, -8
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  store i64 %0, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: argmemonly mustprogress nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly mustprogress nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_IMMImEvRmT_(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %value) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %0, -8
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  store i64 %value, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_IMMIjEvRmT_(i64* nonnull align 8 dereferenceable(8) %vsp, i32 %value) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %0, -4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  store i32 %value, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_IMMItEvRmT_(i64* nonnull align 8 dereferenceable(8) %vsp, i16 zeroext %value) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %0, -2
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  store i16 %value, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_VSPILm64EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %0, -8
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  store i64 %0, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_VSPILm32EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %conv = trunc i64 %0 to i32
  %sub.i = add i64 %0, -4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  store i32 %conv, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z8PUSH_VSPILm16EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %conv = trunc i64 %0 to i16
  %sub.i = add i64 %0, -2
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  store i16 %conv, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7POP_VSPILm64EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  store i64 %value.0.copyload.i, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7POP_VSPILm32EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  %and = and i64 %add.i, -4294967296
  %conv = zext i32 %value.0.copyload.i to i64
  %or = or i64 %and, %conv
  store i64 %or, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7POP_VSPILm16EEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  %and = and i64 %add.i, -65536
  %conv = zext i16 %value.0.copyload.i to i64
  %or = or i64 %and, %conv
  store i64 %or, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z9POP_FLAGSRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %flags) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  store i64 %value.0.copyload.i, i64* %flags, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4LOADImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  %value.0.copyload = load i64, i64* %value.0.arrayidx.sroa_cast, align 1
  store i64 %2, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i64*
  store i64 %value.0.copyload, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4LOADIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %value.0.copyload = load i32, i32* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i32*
  store i32 %value.0.copyload, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4LOADItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i16*
  store i16 %value.0.copyload, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4LOADIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.copyload = load i8, i8* %arrayidx, align 1
  %conv.i = zext i8 %value.0.copyload to i16
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i6 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i6 to i16*
  store i16 %conv.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_GSImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @GS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  %value.0.copyload = load i64, i64* %value.0.arrayidx.sroa_cast, align 1
  store i64 %2, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i64*
  store i64 %value.0.copyload, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_GSIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @GS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %value.0.copyload = load i32, i32* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i32*
  store i32 %value.0.copyload, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_GSItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @GS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i16*
  store i16 %value.0.copyload, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_GSIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @GS, i64 0, i64 %value.0.copyload.i
  %value.0.copyload = load i8, i8* %arrayidx, align 1
  %conv.i = zext i8 %value.0.copyload to i16
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i6 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i6 to i16*
  store i16 %conv.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_FSImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @FS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  %value.0.copyload = load i64, i64* %value.0.arrayidx.sroa_cast, align 1
  store i64 %2, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i64*
  store i64 %value.0.copyload, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_FSIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @FS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %value.0.copyload = load i32, i32* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i32*
  store i32 %value.0.copyload, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_FSItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @FS, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i7 to i16*
  store i16 %value.0.copyload, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z7LOAD_FSIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @FS, i64 0, i64 %value.0.copyload.i
  %value.0.copyload = load i8, i8* %arrayidx, align 1
  %conv.i = zext i8 %value.0.copyload to i16
  %sub.i = add i64 %2, 6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i6 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i6 to i16*
  store i16 %conv.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z5STOREImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i8 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i9 = bitcast i8* %arrayidx.i8 to i64*
  %value.0.copyload.i10 = load i64, i64* %value.0.arrayidx.sroa_cast.i9, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i9, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i11 = add i64 %4, 8
  store i64 %add.i11, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  store i64 %value.0.copyload.i10, i64* %value.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z5STOREIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i8 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i9 = bitcast i8* %arrayidx.i8 to i32*
  %value.0.copyload.i10 = load i32, i32* %value.0.arrayidx.sroa_cast.i9, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %3 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i9, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i11 = add i64 %4, 4
  store i64 %add.i11, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  store i32 %value.0.copyload.i10, i32* %value.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z5STOREItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i8 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i9 = bitcast i8* %arrayidx.i8 to i16*
  %value.0.copyload.i10 = load i16, i16* %value.0.arrayidx.sroa_cast.i9, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %3 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i9, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i11 = add i64 %4, 2
  store i64 %add.i11, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  store i16 %value.0.copyload.i10, i16* %value.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z5STOREIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i7 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i8 = bitcast i8* %arrayidx.i7 to i16*
  %value.0.copyload.i9 = load i16, i16* %value.0.arrayidx.sroa_cast.i8, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %3 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i8, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i10 = add i64 %4, 2
  store i64 %add.i10, i64* %vsp, align 8, !tbaa !4
  %conv.i = trunc i16 %value.0.copyload.i9 to i8
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %value.0.copyload.i
  store i8 %conv.i, i8* %arrayidx, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm8ELm0EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %vmreg.sroa.0.0.extract.trunc = trunc i64 %vmreg.coerce to i16
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %conv.i = and i16 %vmreg.sroa.0.0.extract.trunc, 255
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %byte.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  store i16 %conv.i, i16* %byte.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm8ELm1EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %vmreg.sroa.1.0.extract.shift = lshr i64 %vmreg.coerce, 8
  %vmreg.sroa.1.0.extract.trunc = trunc i64 %vmreg.sroa.1.0.extract.shift to i16
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %conv.i = and i16 %vmreg.sroa.1.0.extract.trunc, 255
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %byte.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  store i16 %conv.i, i16* %byte.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm16ELm0EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %vmreg.sroa.0.0.extract.trunc = trunc i64 %vmreg.coerce to i16
  store i16 %vmreg.sroa.0.0.extract.trunc, i16* %vmreg.sroa.0.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm16ELm1EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.2.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %vmreg.sroa.0.2.extract.shift = lshr i64 %vmreg.coerce, 16
  %vmreg.sroa.0.2.extract.trunc = trunc i64 %vmreg.sroa.0.2.extract.shift to i16
  store i16 %vmreg.sroa.0.2.extract.trunc, i16* %vmreg.sroa.0.2.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm16ELm2EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.4.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %vmreg.sroa.0.4.extract.shift = lshr i64 %vmreg.coerce, 32
  %vmreg.sroa.0.4.extract.trunc = trunc i64 %vmreg.sroa.0.4.extract.shift to i16
  store i16 %vmreg.sroa.0.4.extract.trunc, i16* %vmreg.sroa.0.4.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm16ELm3EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -2
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.6.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %vmreg.sroa.0.6.extract.shift = lshr i64 %vmreg.coerce, 48
  %vmreg.sroa.0.6.extract.trunc = trunc i64 %vmreg.sroa.0.6.extract.shift to i16
  store i16 %vmreg.sroa.0.6.extract.trunc, i16* %vmreg.sroa.0.6.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm32ELm0EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -4
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %vmreg.sroa.0.0.extract.trunc = trunc i64 %vmreg.coerce to i32
  store i32 %vmreg.sroa.0.0.extract.trunc, i32* %vmreg.sroa.0.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm32ELm1EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -4
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.4.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %vmreg.sroa.0.4.extract.shift = lshr i64 %vmreg.coerce, 32
  %vmreg.sroa.0.4.extract.trunc = trunc i64 %vmreg.sroa.0.4.extract.shift to i32
  store i32 %vmreg.sroa.0.4.extract.trunc, i32* %vmreg.sroa.0.4.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z10PUSH_VMREGILm64ELm0EEvRm15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, i64 %vmreg.coerce) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %0, -8
  store i64 %sub, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub
  %vmreg.sroa.0.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  store i64 %vmreg.coerce, i64* %vmreg.sroa.0.0.arrayidx.sroa_cast, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm8ELm0EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %byte.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %byte.0.copyload = load i16, i16* %byte.0.arrayidx.sroa_cast, align 1
  %conv.i = trunc i16 %byte.0.copyload to i8
  %b0 = bitcast %struct.VirtualRegister* %vmreg to i8*
  store i8 %conv.i, i8* %b0, align 1, !tbaa !8
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i8 = trunc i64 %1 to i16
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx3 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %undef.0.arrayidx3.sroa_cast = bitcast i8* %arrayidx3 to i16*
  store i16 %conv.i8, i16* %undef.0.arrayidx3.sroa_cast, align 1
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %3, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm8ELm1EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %byte.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %byte.0.copyload = load i16, i16* %byte.0.arrayidx.sroa_cast, align 1
  %conv.i = trunc i16 %byte.0.copyload to i8
  %byte1 = bitcast %struct.VirtualRegister* %vmreg to %struct.anon*
  %b1 = getelementptr inbounds %struct.anon, %struct.anon* %byte1, i64 0, i32 1
  store i8 %conv.i, i8* %b1, align 1, !tbaa !8
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i8 = trunc i64 %1 to i16
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx3 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %undef.0.arrayidx3.sroa_cast = bitcast i8* %arrayidx3 to i16*
  store i16 %conv.i8, i16* %undef.0.arrayidx3.sroa_cast, align 1
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %3, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm16ELm0EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, -65536
  %conv = zext i16 %value.0.copyload to i64
  %or = or i64 %and, %conv
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %2 to i16
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx2 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx2.sroa_cast = bitcast i8* %arrayidx2 to i16*
  store i16 %conv.i, i16* %undef.0.arrayidx2.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm16ELm1EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, -4294901761
  %conv.i = zext i16 %value.0.copyload to i64
  %shl.i = shl nuw nsw i64 %conv.i, 16
  %or = or i64 %and, %shl.i
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i10 = trunc i64 %2 to i16
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx4 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx4.sroa_cast = bitcast i8* %arrayidx4 to i16*
  store i16 %conv.i10, i16* %undef.0.arrayidx4.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm16ELm2EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, -281470681743361
  %conv.i = zext i16 %value.0.copyload to i64
  %shl.i = shl nuw nsw i64 %conv.i, 32
  %or = or i64 %and, %shl.i
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i10 = trunc i64 %2 to i16
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx4 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx4.sroa_cast = bitcast i8* %arrayidx4 to i16*
  store i16 %conv.i10, i16* %undef.0.arrayidx4.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm16ELm3EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i16*
  %value.0.copyload = load i16, i16* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, 281474976710655
  %conv.i = zext i16 %value.0.copyload to i64
  %shl.i = shl nuw i64 %conv.i, 48
  %or = or i64 %and, %shl.i
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i10 = trunc i64 %2 to i16
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx4 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx4.sroa_cast = bitcast i8* %arrayidx4 to i16*
  store i16 %conv.i10, i16* %undef.0.arrayidx4.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 2
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm32ELm0EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %value.0.copyload = load i32, i32* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, -4294967296
  %conv = zext i32 %value.0.copyload to i64
  %or = or i64 %and, %conv
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %2 to i32
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx2 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx2.sroa_cast = bitcast i8* %arrayidx2 to i32*
  store i32 %conv.i, i32* %undef.0.arrayidx2.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 4
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm32ELm1EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i32*
  %value.0.copyload = load i32, i32* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  %1 = load i64, i64* %qword, align 1, !tbaa !8
  %and = and i64 %1, 4294967295
  %conv.i = zext i32 %value.0.copyload to i64
  %shl.i = shl nuw i64 %conv.i, 32
  %or = or i64 %and, %shl.i
  store i64 %or, i64* %qword, align 1, !tbaa !8
  %2 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i10 = trunc i64 %2 to i32
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx4 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %3
  %undef.0.arrayidx4.sroa_cast = bitcast i8* %arrayidx4 to i32*
  store i32 %conv.i10, i32* %undef.0.arrayidx4.sroa_cast, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %4, 4
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z9POP_VMREGILm64ELm0EEvRmR15VirtualRegister(i64* nonnull align 8 dereferenceable(8) %vsp, %struct.VirtualRegister* nonnull align 1 dereferenceable(8) %vmreg) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast = bitcast i8* %arrayidx to i64*
  %value.0.copyload = load i64, i64* %value.0.arrayidx.sroa_cast, align 1
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  store i64 %value.0.copyload, i64* %qword, align 1, !tbaa !8
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx1 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %undef.0.arrayidx1.sroa_cast = bitcast i8* %arrayidx1 to i64*
  store i64 %1, i64* %undef.0.arrayidx1.sroa_cast, align 1
  %3 = load i64, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %3, 8
  store i64 %add, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z8PUSH_REGRmm(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64 %reg) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %0, -8
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  store i64 %reg, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z7POP_REGRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %reg) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  store i64 %value.0.copyload.i, i64* %reg, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z8POP_VOIDRm(i64* nocapture nonnull align 8 dereferenceable(8) %vsp) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z15MOVE_VMREG_SLOTR15VirtualRegisterRm(%struct.VirtualRegister* nocapture nonnull align 1 dereferenceable(8) %vmreg, i64* nocapture nonnull readonly align 8 dereferenceable(8) %slot) #2 {
entry:
  %0 = load i64, i64* %slot, align 8, !tbaa !4
  %qword = getelementptr inbounds %struct.VirtualRegister, %struct.VirtualRegister* %vmreg, i64 0, i32 0, i32 0
  store i64 %0, i64* %qword, align 1, !tbaa !8
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z8POP_SLOTRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %slot) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  store i64 %value.0.copyload.i, i64* %slot, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define dso_local void @_Z5CPUIDRm(i64* nocapture nonnull align 8 dereferenceable(8) %vsp) #0 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %3 = tail call { i32, i32, i32, i32 } asm "  xchgq  %rbx,${1:q}\0A  cpuid\0A  xchgq  %rbx,${1:q}", "={ax},=r,={cx},={dx},0,~{dirflag},~{fpsr},~{flags}"(i32 %value.0.copyload.i) #11, !srcloc !9
  %asmresult = extractvalue { i32, i32, i32, i32 } %3, 0
  %asmresult1 = extractvalue { i32, i32, i32, i32 } %3, 1
  %asmresult2 = extractvalue { i32, i32, i32, i32 } %3, 2
  %asmresult3 = extractvalue { i32, i32, i32, i32 } %3, 3
  %arrayidx.i13 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %2
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i13 to i32*
  store i32 %asmresult, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i14 = add i64 %4, -4
  store i64 %sub.i14, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i15 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i14
  %value.addr.0.arrayidx.sroa_cast.i16 = bitcast i8* %arrayidx.i15 to i32*
  store i32 %asmresult1, i32* %value.addr.0.arrayidx.sroa_cast.i16, align 1
  %5 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i17 = add i64 %5, -4
  store i64 %sub.i17, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i18 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i17
  %value.addr.0.arrayidx.sroa_cast.i19 = bitcast i8* %arrayidx.i18 to i32*
  store i32 %asmresult2, i32* %value.addr.0.arrayidx.sroa_cast.i19, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i20 = add i64 %6, -4
  store i64 %sub.i20, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i21 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i20
  %value.addr.0.arrayidx.sroa_cast.i22 = bitcast i8* %arrayidx.i21 to i32*
  store i32 %asmresult3, i32* %value.addr.0.arrayidx.sroa_cast.i22, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define dso_local void @_Z5RDTSCRm(i64* nocapture nonnull align 8 dereferenceable(8) %vsp) #0 {
entry:
  %0 = tail call i64 @llvm.x86.rdtsc()
  %conv = trunc i64 %0 to i32
  %shr.i = lshr i64 %0, 32
  %conv3 = trunc i64 %shr.i to i32
  %1 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i = add i64 %1, -4
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  store i32 %conv, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i11 = add i64 %2, -4
  store i64 %sub.i11, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i12 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i11
  %value.addr.0.arrayidx.sroa_cast.i13 = bitcast i8* %arrayidx.i12 to i32*
  store i32 %conv3, i32* %value.addr.0.arrayidx.sroa_cast.i13, align 1
  ret void
}

; Function Attrs: nounwind
declare i64 @llvm.x86.rdtsc() #3

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z13UPDATE_EFLAGSRmbbbbbb(i64* nocapture nonnull align 8 dereferenceable(8) %flags, i1 zeroext %cf, i1 zeroext %pf, i1 zeroext %af, i1 zeroext %zf, i1 zeroext %sf, i1 zeroext %of) local_unnamed_addr #2 {
entry:
  %0 = load i64, i64* %flags, align 8, !tbaa !4
  %conv = zext i1 %cf to i64
  %or6 = or i64 %0, %conv
  %shl10 = select i1 %pf, i64 4, i64 0
  %shl16 = select i1 %af, i64 16, i64 0
  %and13 = or i64 %shl16, %shl10
  %or17 = or i64 %and13, %or6
  %shl22 = select i1 %zf, i64 64, i64 0
  %shl28 = select i1 %sf, i64 128, i64 0
  %shl34 = select i1 %of, i64 2048, i64 0
  %and25 = or i64 %shl28, %shl22
  %or29 = or i64 %and25, %shl34
  %or30 = or i64 %or29, %or17
  store i64 %or30, i64* %flags, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3ADDImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i28 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i29 = bitcast i8* %arrayidx.i28 to i64*
  %value.0.copyload.i30 = load i64, i64* %value.0.arrayidx.sroa_cast.i29, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i29, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i32 = add i64 %value.0.copyload.i30, %value.0.copyload.i
  %cmp.i.i.i = icmp ult i64 %add.i32, %value.0.copyload.i
  %cmp1.i.i.i = icmp ult i64 %add.i32, %value.0.copyload.i30
  %5 = or i1 %cmp.i.i.i, %cmp1.i.i.i
  %conv.i.i.i = trunc i64 %add.i32 to i8
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %xor.i.i.i = xor i64 %value.0.copyload.i30, %value.0.copyload.i
  %xor1.i.i.i = xor i64 %xor.i.i.i, %add.i32
  %and.i.i.i = and i64 %xor1.i.i.i, 16
  %cmp.i.i25.i = icmp eq i64 %add.i32, 0
  %shr.i.i.i = lshr i64 %value.0.copyload.i, 63
  %shr1.i.i.i = lshr i64 %value.0.copyload.i30, 63
  %shr2.i.i.i = lshr i64 %add.i32, 63
  %xor.i.i27.i = xor i64 %shr2.i.i.i, %shr.i.i.i
  %xor3.i.i.i = xor i64 %shr2.i.i.i, %shr1.i.i.i
  %add.i.i.i = add nuw nsw i64 %xor.i.i27.i, %xor3.i.i.i
  %cmp.i.i28.i = icmp eq i64 %add.i.i.i, 2
  %conv.i.i = zext i1 %5 to i64
  %7 = shl nuw nsw i8 %6, 2
  %8 = and i8 %7, 4
  %9 = xor i8 %8, 4
  %10 = zext i8 %9 to i64
  %shl22.i.i = select i1 %cmp.i.i25.i, i64 64, i64 0
  %11 = lshr i64 %add.i32, 56
  %12 = and i64 %11, 128
  %shl34.i.i = select i1 %cmp.i.i28.i, i64 2048, i64 0
  %or6.i.i = or i64 %12, %shl22.i.i
  %and13.i.i = or i64 %or6.i.i, %and.i.i.i
  %or17.i.i = or i64 %and13.i.i, %conv.i.i
  %and25.i.i = or i64 %or17.i.i, %shl34.i.i
  %or29.i.i = or i64 %and25.i.i, %10
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i33 to i64*
  store i64 %add.i32, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i34 = add i64 %13, -8
  store i64 %sub.i34, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i35 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i34
  %value.addr.0.arrayidx.sroa_cast.i36 = bitcast i8* %arrayidx.i35 to i64*
  store i64 %or29.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i36, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3ADDIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i28 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i29 = bitcast i8* %arrayidx.i28 to i32*
  %value.0.copyload.i30 = load i32, i32* %value.0.arrayidx.sroa_cast.i29, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i31 = trunc i64 %3 to i32
  store i32 %conv.i.i31, i32* %value.0.arrayidx.sroa_cast.i29, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i33 = add i32 %value.0.copyload.i30, %value.0.copyload.i
  %cmp.i.i.i = icmp ult i32 %add.i33, %value.0.copyload.i
  %cmp1.i.i.i = icmp ult i32 %add.i33, %value.0.copyload.i30
  %5 = or i1 %cmp.i.i.i, %cmp1.i.i.i
  %conv.i.i.i = trunc i32 %add.i33 to i8
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %xor.i.i.i = xor i32 %value.0.copyload.i30, %value.0.copyload.i
  %xor1.i.i.i = xor i32 %xor.i.i.i, %add.i33
  %and.i.i.i = and i32 %xor1.i.i.i, 16
  %cmp.i.i25.i = icmp eq i32 %add.i33, 0
  %shr.i.i.i = lshr i32 %value.0.copyload.i, 31
  %shr1.i.i.i = lshr i32 %value.0.copyload.i30, 31
  %shr2.i.i.i = lshr i32 %add.i33, 31
  %xor.i.i27.i = xor i32 %shr2.i.i.i, %shr.i.i.i
  %xor3.i.i.i = xor i32 %shr2.i.i.i, %shr1.i.i.i
  %add.i.i.i = add nuw nsw i32 %xor.i.i27.i, %xor3.i.i.i
  %cmp.i.i28.i = icmp eq i32 %add.i.i.i, 2
  %conv.i.i34 = zext i1 %5 to i64
  %7 = shl nuw nsw i8 %6, 2
  %8 = and i8 %7, 4
  %9 = xor i8 %8, 4
  %10 = zext i8 %9 to i64
  %11 = zext i32 %and.i.i.i to i64
  %shl22.i.i = select i1 %cmp.i.i25.i, i64 64, i64 0
  %12 = lshr i32 %add.i33, 24
  %13 = and i32 %12, 128
  %14 = zext i32 %13 to i64
  %shl34.i.i = select i1 %cmp.i.i28.i, i64 2048, i64 0
  %or6.i.i = or i64 %shl22.i.i, %14
  %and13.i.i = or i64 %or6.i.i, %11
  %or17.i.i = or i64 %and13.i.i, %conv.i.i34
  %and25.i.i = or i64 %or17.i.i, %shl34.i.i
  %or29.i.i = or i64 %and25.i.i, %10
  %arrayidx.i35 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i35 to i32*
  store i32 %add.i33, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %15 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i36 = add i64 %15, -8
  store i64 %sub.i36, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i37 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i36
  %value.addr.0.arrayidx.sroa_cast.i38 = bitcast i8* %arrayidx.i37 to i64*
  store i64 %or29.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i38, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3ADDItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i28 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i29 = bitcast i8* %arrayidx.i28 to i16*
  %value.0.copyload.i30 = load i16, i16* %value.0.arrayidx.sroa_cast.i29, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i31 = trunc i64 %3 to i16
  store i16 %conv.i.i31, i16* %value.0.arrayidx.sroa_cast.i29, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i33 = add i16 %value.0.copyload.i30, %value.0.copyload.i
  %cmp.i.i.i = icmp ult i16 %add.i33, %value.0.copyload.i
  %cmp4.i.i.i = icmp ult i16 %add.i33, %value.0.copyload.i30
  %5 = or i1 %cmp.i.i.i, %cmp4.i.i.i
  %conv.i.i.i = trunc i16 %add.i33 to i8
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %xor4.i.i.i = xor i16 %value.0.copyload.i30, %value.0.copyload.i
  %xor35.i.i.i = xor i16 %xor4.i.i.i, %add.i33
  %7 = and i16 %xor35.i.i.i, 16
  %cmp.i.i25.i = icmp eq i16 %add.i33, 0
  %8 = lshr i16 %value.0.copyload.i, 15
  %9 = lshr i16 %value.0.copyload.i30, 15
  %10 = lshr i16 %add.i33, 15
  %xor17.i.i.i = xor i16 %10, %8
  %xor1218.i.i.i = xor i16 %10, %9
  %narrow.i.i.i = add nuw nsw i16 %xor17.i.i.i, %xor1218.i.i.i
  %cmp.i.i27.i = icmp eq i16 %narrow.i.i.i, 2
  %conv.i.i34 = zext i1 %5 to i64
  %11 = shl nuw nsw i8 %6, 2
  %12 = and i8 %11, 4
  %13 = xor i8 %12, 4
  %14 = zext i8 %13 to i64
  %15 = zext i16 %7 to i64
  %shl22.i.i = select i1 %cmp.i.i25.i, i64 64, i64 0
  %16 = lshr i16 %add.i33, 8
  %17 = and i16 %16, 128
  %18 = zext i16 %17 to i64
  %shl34.i.i = select i1 %cmp.i.i27.i, i64 2048, i64 0
  %or6.i.i = or i64 %shl22.i.i, %18
  %and13.i.i = or i64 %or6.i.i, %15
  %or17.i.i = or i64 %and13.i.i, %conv.i.i34
  %and25.i.i = or i64 %or17.i.i, %shl34.i.i
  %or29.i.i = or i64 %and25.i.i, %14
  %arrayidx.i35 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i35 to i16*
  store i16 %add.i33, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %19 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i36 = add i64 %19, -8
  store i64 %sub.i36, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i37 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i36
  %value.addr.0.arrayidx.sroa_cast.i38 = bitcast i8* %arrayidx.i37 to i64*
  store i64 %or29.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i38, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3ADDIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %conv.i = trunc i16 %value.0.copyload.i to i8
  %arrayidx.i23 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i24 = bitcast i8* %arrayidx.i23 to i16*
  %value.0.copyload.i25 = load i16, i16* %value.0.arrayidx.sroa_cast.i24, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i26 = trunc i64 %3 to i16
  store i16 %conv.i.i26, i16* %value.0.arrayidx.sroa_cast.i24, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %conv.i28 = trunc i16 %value.0.copyload.i25 to i8
  %add.i29 = add i8 %conv.i28, %conv.i
  %cmp.i.i.i = icmp ult i8 %add.i29, %conv.i
  %cmp4.i.i.i = icmp ult i8 %add.i29, %conv.i28
  %5 = or i1 %cmp.i.i.i, %cmp4.i.i.i
  %6 = tail call i8 @llvm.ctpop.i8(i8 %add.i29) #3, !range !10
  %xor4.i.i.i38 = xor i16 %value.0.copyload.i25, %value.0.copyload.i
  %xor4.i.i.i = trunc i16 %xor4.i.i.i38 to i8
  %xor35.i.i.i = xor i8 %add.i29, %xor4.i.i.i
  %7 = and i8 %xor35.i.i.i, 16
  %cmp.i.i25.i = icmp eq i8 %add.i29, 0
  %8 = lshr i8 %conv.i, 7
  %9 = lshr i8 %conv.i28, 7
  %10 = lshr i8 %add.i29, 7
  %xor14.i.i.i = xor i8 %10, %8
  %xor1215.i.i.i = xor i8 %10, %9
  %narrow.i.i.i = add nuw nsw i8 %xor14.i.i.i, %xor1215.i.i.i
  %cmp.i.i27.i = icmp eq i8 %narrow.i.i.i, 2
  %conv.i.i30 = zext i1 %5 to i64
  %11 = shl nuw nsw i8 %6, 2
  %12 = and i8 %11, 4
  %13 = or i8 %12, %7
  %and13.i28.i = xor i8 %13, 4
  %and13.i.i = zext i8 %and13.i28.i to i64
  %shl22.i.i = select i1 %cmp.i.i25.i, i64 64, i64 0
  %14 = and i8 %add.i29, -128
  %15 = zext i8 %14 to i64
  %shl34.i.i = select i1 %cmp.i.i27.i, i64 2048, i64 0
  %or6.i.i = or i64 %shl22.i.i, %15
  %or17.i.i = or i64 %or6.i.i, %conv.i.i30
  %and25.i.i = or i64 %or17.i.i, %shl34.i.i
  %or29.i.i = or i64 %and25.i.i, %and13.i.i
  %conv.i31 = zext i8 %add.i29 to i16
  %arrayidx.i32 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i32 to i16*
  store i16 %conv.i31, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %16 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i33 = add i64 %16, -8
  store i64 %sub.i33, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i34 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i33
  %value.addr.0.arrayidx.sroa_cast.i35 = bitcast i8* %arrayidx.i34 to i64*
  store i64 %or29.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i35, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z9DIV_FLAGSRm(i64* nocapture nonnull align 8 dereferenceable(8) %flags) local_unnamed_addr #2 {
entry:
  %0 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %0 to i8
  %tobool = icmp ne i8 %conv.i, 0
  %1 = load i64, i64* %flags, align 8, !tbaa !4
  %conv.i27 = zext i1 %tobool to i64
  %or6.i = or i64 %1, %conv.i27
  %and13.i = select i1 %tobool, i64 20, i64 0
  %or17.i = or i64 %or6.i, %and13.i
  %or29.i = select i1 %tobool, i64 2240, i64 0
  %or30.i = or i64 %or17.i, %or29.i
  store i64 %or30.i, i64* %flags, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3DIVImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i64 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i65 = bitcast i8* %arrayidx.i64 to i64*
  %value.0.copyload.i66126127 = load i64, i64* %value.0.arrayidx.sroa_cast.i65, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i65, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i67 = add i64 %4, 8
  store i64 %add.i67, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i68 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i67
  %value.0.arrayidx.sroa_cast.i69 = bitcast i8* %arrayidx.i68 to i64*
  %value.0.copyload.i70 = load i64, i64* %value.0.arrayidx.sroa_cast.i69, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %5, i64* %value.0.arrayidx.sroa_cast.i69, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i71 = add i64 %6, 8
  store i64 %add.i71, i64* %vsp, align 8, !tbaa !4
  %L.sroa.2.0.insert.ext.i91 = zext i64 %value.0.copyload.i66126127 to i128
  %L.sroa.2.0.insert.shift.i92 = shl nuw i128 %L.sroa.2.0.insert.ext.i91, 64
  %L.sroa.0.0.insert.ext.i93 = zext i64 %value.0.copyload.i to i128
  %L.sroa.0.0.insert.insert.i94 = or i128 %L.sroa.2.0.insert.shift.i92, %L.sroa.0.0.insert.ext.i93
  %R.sroa.0.0.insert.ext.i97 = zext i64 %value.0.copyload.i70 to i128
  %L.sroa.0.0.insert.insert.i94.frozen = freeze i128 %L.sroa.0.0.insert.insert.i94
  %R.sroa.0.0.insert.ext.i97.frozen = freeze i128 %R.sroa.0.0.insert.ext.i97
  %div.i = udiv i128 %L.sroa.0.0.insert.insert.i94.frozen, %R.sroa.0.0.insert.ext.i97.frozen
  %retval.sroa.0.0.extract.trunc.i99 = trunc i128 %div.i to i64
  %7 = mul i128 %div.i, %R.sroa.0.0.insert.ext.i97.frozen
  %rem.i.decomposed = sub i128 %L.sroa.0.0.insert.insert.i94.frozen, %7
  %retval.sroa.0.0.extract.trunc.i112 = trunc i128 %rem.i.decomposed to i64
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %8 to i8
  %tobool.i = icmp ne i8 %conv.i.i, 0
  %conv.i27.i = zext i1 %tobool.i to i64
  %and13.i.i = select i1 %tobool.i, i64 20, i64 0
  %or17.i.i = or i64 %and13.i.i, %conv.i27.i
  %or29.i.i = select i1 %tobool.i, i64 2240, i64 0
  %or30.i.i = or i64 %or17.i.i, %or29.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i117 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i117 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i99, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i118 = add i64 %9, -8
  store i64 %sub.i118, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i119 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i118
  %value.addr.0.arrayidx.sroa_cast.i120 = bitcast i8* %arrayidx.i119 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i112, i64* %value.addr.0.arrayidx.sroa_cast.i120, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i121 = add i64 %10, -8
  store i64 %sub.i121, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i122 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i121
  %value.addr.0.arrayidx.sroa_cast.i123 = bitcast i8* %arrayidx.i122 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i123, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3DIVIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i32*
  %value.0.copyload.i49 = load i32, i32* %value.0.arrayidx.sroa_cast.i48, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i50 = trunc i64 %3 to i32
  store i32 %conv.i.i50, i32* %value.0.arrayidx.sroa_cast.i48, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i51 = add i64 %4, 4
  store i64 %add.i51, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i52 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i51
  %value.0.arrayidx.sroa_cast.i53 = bitcast i8* %arrayidx.i52 to i32*
  %value.0.copyload.i54 = load i32, i32* %value.0.arrayidx.sroa_cast.i53, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i55 = trunc i64 %5 to i32
  store i32 %conv.i.i55, i32* %value.0.arrayidx.sroa_cast.i53, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %6, 4
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i32 %value.0.copyload.i to i64
  %conv.i57 = zext i32 %value.0.copyload.i49 to i64
  %conv.i58 = zext i32 %value.0.copyload.i54 to i64
  %shl.i = shl nuw i64 %conv.i57, 32
  %or.i = or i64 %shl.i, %conv.i
  %div.i = udiv i64 %or.i, %conv.i58
  %rem.i = urem i64 %or.i, %conv.i58
  %conv.i59 = trunc i64 %div.i to i32
  %conv.i60 = trunc i64 %rem.i to i32
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i61 = trunc i64 %7 to i8
  %tobool.i = icmp ne i8 %conv.i.i61, 0
  %conv.i27.i = zext i1 %tobool.i to i64
  %and13.i.i = select i1 %tobool.i, i64 20, i64 0
  %or17.i.i = or i64 %and13.i.i, %conv.i27.i
  %or29.i.i = select i1 %tobool.i, i64 2240, i64 0
  %or30.i.i = or i64 %or17.i.i, %or29.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i62 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i62 to i32*
  store i32 %conv.i59, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i63 = add i64 %8, -4
  store i64 %sub.i63, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i64 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i63
  %value.addr.0.arrayidx.sroa_cast.i65 = bitcast i8* %arrayidx.i64 to i32*
  store i32 %conv.i60, i32* %value.addr.0.arrayidx.sroa_cast.i65, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i66 = add i64 %9, -8
  store i64 %sub.i66, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i67 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i66
  %value.addr.0.arrayidx.sroa_cast.i68 = bitcast i8* %arrayidx.i67 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i68, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3DIVItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i16*
  %value.0.copyload.i49 = load i16, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i50 = trunc i64 %3 to i16
  store i16 %conv.i.i50, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i51 = add i64 %4, 2
  store i64 %add.i51, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i52 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i51
  %value.0.arrayidx.sroa_cast.i53 = bitcast i8* %arrayidx.i52 to i16*
  %value.0.copyload.i54 = load i16, i16* %value.0.arrayidx.sroa_cast.i53, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i55 = trunc i64 %5 to i16
  store i16 %conv.i.i55, i16* %value.0.arrayidx.sroa_cast.i53, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %6, 2
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i16 %value.0.copyload.i to i32
  %conv.i58 = zext i16 %value.0.copyload.i54 to i32
  %conv.i59 = zext i16 %value.0.copyload.i49 to i32
  %shl.i = shl nuw i32 %conv.i59, 16
  %or3.i = or i32 %shl.i, %conv.i
  %7 = udiv i32 %or3.i, %conv.i58
  %8 = urem i32 %or3.i, %conv.i58
  %conv.i60 = trunc i32 %7 to i16
  %conv.i61 = trunc i32 %8 to i16
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i62 = trunc i64 %9 to i8
  %tobool.i = icmp ne i8 %conv.i.i62, 0
  %conv.i27.i = zext i1 %tobool.i to i64
  %and13.i.i = select i1 %tobool.i, i64 20, i64 0
  %or17.i.i = or i64 %and13.i.i, %conv.i27.i
  %or29.i.i = select i1 %tobool.i, i64 2240, i64 0
  %or30.i.i = or i64 %or17.i.i, %or29.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i63 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i63 to i16*
  store i16 %conv.i60, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i64 = add i64 %10, -2
  store i64 %sub.i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i65 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i64
  %value.addr.0.arrayidx.sroa_cast.i66 = bitcast i8* %arrayidx.i65 to i16*
  store i16 %conv.i61, i16* %value.addr.0.arrayidx.sroa_cast.i66, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i67 = add i64 %11, -8
  store i64 %sub.i67, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i68 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i67
  %value.addr.0.arrayidx.sroa_cast.i69 = bitcast i8* %arrayidx.i68 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i69, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3DIVIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i38 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i39 = bitcast i8* %arrayidx.i38 to i16*
  %value.0.copyload.i40 = load i16, i16* %value.0.arrayidx.sroa_cast.i39, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i41 = trunc i64 %3 to i16
  store i16 %conv.i.i41, i16* %value.0.arrayidx.sroa_cast.i39, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i42 = add i64 %4, 2
  store i64 %add.i42, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i44 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i42
  %value.0.arrayidx.sroa_cast.i45 = bitcast i8* %arrayidx.i44 to i16*
  %value.0.copyload.i46 = load i16, i16* %value.0.arrayidx.sroa_cast.i45, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i47 = trunc i64 %5 to i16
  store i16 %conv.i.i47, i16* %value.0.arrayidx.sroa_cast.i45, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i48 = add i64 %6, 2
  store i64 %add.i48, i64* %vsp, align 8, !tbaa !4
  %conv.i50 = and i16 %value.0.copyload.i, 255
  %conv.i52 = and i16 %value.0.copyload.i46, 255
  %7 = shl i16 %value.0.copyload.i40, 8
  %or3.i = or i16 %7, %conv.i50
  %8 = udiv i16 %or3.i, %conv.i52
  %9 = urem i16 %or3.i, %conv.i52
  %conv.i54 = trunc i16 %8 to i8
  %conv.i55 = trunc i16 %9 to i8
  %10 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i56 = trunc i64 %10 to i8
  %tobool.i = icmp ne i8 %conv.i.i56, 0
  %conv.i27.i = zext i1 %tobool.i to i64
  %and13.i.i = select i1 %tobool.i, i64 20, i64 0
  %or17.i.i = or i64 %and13.i.i, %conv.i27.i
  %or29.i.i = select i1 %tobool.i, i64 2240, i64 0
  %or30.i.i = or i64 %or17.i.i, %or29.i.i
  %sub.i = add i64 %6, 1
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  store i8 %conv.i54, i8* %arrayidx.i57, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i58 = add i64 %11, -1
  store i64 %sub.i58, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i58
  store i8 %conv.i55, i8* %arrayidx.i59, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i60 = add i64 %12, -8
  store i64 %sub.i60, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i61 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i60
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i61 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z10IDIV_FLAGSRm(i64* nocapture nonnull align 8 dereferenceable(8) %flags) local_unnamed_addr #2 {
entry:
  %0 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %0 to i8
  %tobool.i = icmp ne i8 %conv.i.i, 0
  %1 = load i64, i64* %flags, align 8, !tbaa !4
  %conv.i27.i = zext i1 %tobool.i to i64
  %or6.i.i = or i64 %1, %conv.i27.i
  %and13.i.i = select i1 %tobool.i, i64 20, i64 0
  %or17.i.i = or i64 %or6.i.i, %and13.i.i
  %or29.i.i = select i1 %tobool.i, i64 2240, i64 0
  %or30.i.i = or i64 %or17.i.i, %or29.i.i
  store i64 %or30.i.i, i64* %flags, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IDIVImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i69 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i70 = bitcast i8* %arrayidx.i69 to i64*
  %value.0.copyload.i71131132 = load i64, i64* %value.0.arrayidx.sroa_cast.i70, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i70, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i72 = add i64 %4, 8
  store i64 %add.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i72
  %value.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  %value.0.copyload.i75 = load i64, i64* %value.0.arrayidx.sroa_cast.i74, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %5, i64* %value.0.arrayidx.sroa_cast.i74, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i76 = add i64 %6, 8
  store i64 %add.i76, i64* %vsp, align 8, !tbaa !4
  %7 = ashr i64 %value.0.copyload.i75, 63
  %L.sroa.2.0.insert.ext.i96 = zext i64 %value.0.copyload.i71131132 to i128
  %L.sroa.2.0.insert.shift.i97 = shl nuw i128 %L.sroa.2.0.insert.ext.i96, 64
  %L.sroa.0.0.insert.ext.i98 = zext i64 %value.0.copyload.i to i128
  %L.sroa.0.0.insert.insert.i99 = or i128 %L.sroa.2.0.insert.shift.i97, %L.sroa.0.0.insert.ext.i98
  %R.sroa.2.0.insert.ext.i100 = zext i64 %7 to i128
  %R.sroa.2.0.insert.shift.i101 = shl nuw i128 %R.sroa.2.0.insert.ext.i100, 64
  %R.sroa.0.0.insert.ext.i102 = zext i64 %value.0.copyload.i75 to i128
  %R.sroa.0.0.insert.insert.i103 = or i128 %R.sroa.2.0.insert.shift.i101, %R.sroa.0.0.insert.ext.i102
  %L.sroa.0.0.insert.insert.i99.frozen = freeze i128 %L.sroa.0.0.insert.insert.i99
  %R.sroa.0.0.insert.insert.i103.frozen = freeze i128 %R.sroa.0.0.insert.insert.i103
  %div.i = sdiv i128 %L.sroa.0.0.insert.insert.i99.frozen, %R.sroa.0.0.insert.insert.i103.frozen
  %retval.sroa.0.0.extract.trunc.i104 = trunc i128 %div.i to i64
  %8 = mul i128 %div.i, %R.sroa.0.0.insert.insert.i103.frozen
  %rem.i.decomposed = sub i128 %L.sroa.0.0.insert.insert.i99.frozen, %8
  %retval.sroa.0.0.extract.trunc.i117 = trunc i128 %rem.i.decomposed to i64
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %9 to i8
  %tobool.i.i = icmp ne i8 %conv.i.i.i, 0
  %conv.i27.i.i = zext i1 %tobool.i.i to i64
  %and13.i.i.i = select i1 %tobool.i.i, i64 20, i64 0
  %or17.i.i.i = or i64 %and13.i.i.i, %conv.i27.i.i
  %or29.i.i.i = select i1 %tobool.i.i, i64 2240, i64 0
  %or30.i.i.i = or i64 %or17.i.i.i, %or29.i.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i122 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i122 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i104, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i123 = add i64 %10, -8
  store i64 %sub.i123, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i124 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i123
  %value.addr.0.arrayidx.sroa_cast.i125 = bitcast i8* %arrayidx.i124 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i117, i64* %value.addr.0.arrayidx.sroa_cast.i125, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i126 = add i64 %11, -8
  store i64 %sub.i126, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i127 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i126
  %value.addr.0.arrayidx.sroa_cast.i128 = bitcast i8* %arrayidx.i127 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i128, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IDIVIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i32*
  %value.0.copyload.i52 = load i32, i32* %value.0.arrayidx.sroa_cast.i51, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i53 = trunc i64 %3 to i32
  store i32 %conv.i.i53, i32* %value.0.arrayidx.sroa_cast.i51, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i54 = add i64 %4, 4
  store i64 %add.i54, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i55 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i54
  %value.0.arrayidx.sroa_cast.i56 = bitcast i8* %arrayidx.i55 to i32*
  %value.0.copyload.i57 = load i32, i32* %value.0.arrayidx.sroa_cast.i56, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i58 = trunc i64 %5 to i32
  store i32 %conv.i.i58, i32* %value.0.arrayidx.sroa_cast.i56, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i59 = add i64 %6, 4
  store i64 %add.i59, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i32 %value.0.copyload.i to i64
  %conv.i60 = zext i32 %value.0.copyload.i52 to i64
  %conv.i61 = sext i32 %value.0.copyload.i57 to i64
  %shl.i = shl nuw i64 %conv.i60, 32
  %or.i = or i64 %shl.i, %conv.i
  %div.i = sdiv i64 %or.i, %conv.i61
  %rem.i = srem i64 %or.i, %conv.i61
  %conv.i62 = trunc i64 %div.i to i32
  %conv.i63 = trunc i64 %rem.i to i32
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %7 to i8
  %tobool.i.i = icmp ne i8 %conv.i.i.i, 0
  %conv.i27.i.i = zext i1 %tobool.i.i to i64
  %and13.i.i.i = select i1 %tobool.i.i, i64 20, i64 0
  %or17.i.i.i = or i64 %and13.i.i.i, %conv.i27.i.i
  %or29.i.i.i = select i1 %tobool.i.i, i64 2240, i64 0
  %or30.i.i.i = or i64 %or17.i.i.i, %or29.i.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i64 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i64 to i32*
  store i32 %conv.i62, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i65 = add i64 %8, -4
  store i64 %sub.i65, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i66 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i65
  %value.addr.0.arrayidx.sroa_cast.i67 = bitcast i8* %arrayidx.i66 to i32*
  store i32 %conv.i63, i32* %value.addr.0.arrayidx.sroa_cast.i67, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i68 = add i64 %9, -8
  store i64 %sub.i68, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i69 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i68
  %value.addr.0.arrayidx.sroa_cast.i70 = bitcast i8* %arrayidx.i69 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i70, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IDIVItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i16*
  %value.0.copyload.i52 = load i16, i16* %value.0.arrayidx.sroa_cast.i51, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i53 = trunc i64 %3 to i16
  store i16 %conv.i.i53, i16* %value.0.arrayidx.sroa_cast.i51, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i54 = add i64 %4, 2
  store i64 %add.i54, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i55 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i54
  %value.0.arrayidx.sroa_cast.i56 = bitcast i8* %arrayidx.i55 to i16*
  %value.0.copyload.i57 = load i16, i16* %value.0.arrayidx.sroa_cast.i56, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i58 = trunc i64 %5 to i16
  store i16 %conv.i.i58, i16* %value.0.arrayidx.sroa_cast.i56, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i59 = add i64 %6, 2
  store i64 %add.i59, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i16 %value.0.copyload.i to i32
  %conv.i62 = zext i16 %value.0.copyload.i52 to i32
  %shl.i = shl nuw i32 %conv.i62, 16
  %or3.i = or i32 %shl.i, %conv.i
  %conv.i63 = sext i32 %or3.i to i64
  %conv1.i = sext i16 %value.0.copyload.i57 to i64
  %div.i = sdiv i64 %conv.i63, %conv1.i
  %conv2.i64 = trunc i64 %div.i to i16
  %rem.i = srem i64 %conv.i63, %conv1.i
  %conv2.i67 = trunc i64 %rem.i to i16
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %7 to i8
  %tobool.i.i = icmp ne i8 %conv.i.i.i, 0
  %conv.i27.i.i = zext i1 %tobool.i.i to i64
  %and13.i.i.i = select i1 %tobool.i.i, i64 20, i64 0
  %or17.i.i.i = or i64 %and13.i.i.i, %conv.i27.i.i
  %or29.i.i.i = select i1 %tobool.i.i, i64 2240, i64 0
  %or30.i.i.i = or i64 %or17.i.i.i, %or29.i.i.i
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i70 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i70 to i16*
  store i16 %conv2.i64, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i71 = add i64 %8, -2
  store i64 %sub.i71, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i72 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i71
  %value.addr.0.arrayidx.sroa_cast.i73 = bitcast i8* %arrayidx.i72 to i16*
  store i16 %conv2.i67, i16* %value.addr.0.arrayidx.sroa_cast.i73, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i74 = add i64 %9, -8
  store i64 %sub.i74, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i75 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i74
  %value.addr.0.arrayidx.sroa_cast.i76 = bitcast i8* %arrayidx.i75 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i76, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IDIVIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i41 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i42 = bitcast i8* %arrayidx.i41 to i16*
  %value.0.copyload.i43 = load i16, i16* %value.0.arrayidx.sroa_cast.i42, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i44 = trunc i64 %3 to i16
  store i16 %conv.i.i44, i16* %value.0.arrayidx.sroa_cast.i42, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i45 = add i64 %4, 2
  store i64 %add.i45, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i45
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i16*
  %value.0.copyload.i49 = load i16, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i50 = trunc i64 %5 to i16
  store i16 %conv.i.i50, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i51 = add i64 %6, 2
  store i64 %add.i51, i64* %vsp, align 8, !tbaa !4
  %conv.i53 = and i16 %value.0.copyload.i, 255
  %sext = shl i16 %value.0.copyload.i49, 8
  %conv.i55 = ashr exact i16 %sext, 8
  %7 = shl i16 %value.0.copyload.i43, 8
  %or3.i = or i16 %7, %conv.i53
  %conv.i57 = sext i16 %or3.i to i32
  %conv1.i = sext i16 %conv.i55 to i32
  %div3.i = sdiv i32 %conv.i57, %conv1.i
  %div.sext.i = trunc i32 %div3.i to i8
  %rem3.i = srem i32 %conv.i57, %conv1.i
  %rem.sext.i = trunc i32 %rem3.i to i8
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %8 to i8
  %tobool.i.i = icmp ne i8 %conv.i.i.i, 0
  %conv.i27.i.i = zext i1 %tobool.i.i to i64
  %and13.i.i.i = select i1 %tobool.i.i, i64 20, i64 0
  %or17.i.i.i = or i64 %and13.i.i.i, %conv.i27.i.i
  %or29.i.i.i = select i1 %tobool.i.i, i64 2240, i64 0
  %or30.i.i.i = or i64 %or17.i.i.i, %or29.i.i.i
  %sub.i = add i64 %6, 1
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i62 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  store i8 %div.sext.i, i8* %arrayidx.i62, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i63 = add i64 %9, -1
  store i64 %sub.i63, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i64 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i63
  store i8 %rem.sext.i, i8* %arrayidx.i64, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i65 = add i64 %10, -8
  store i64 %sub.i65, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i66 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i65
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i66 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3MULImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i64*
  %value.0.copyload.i52 = load i64, i64* %value.0.arrayidx.sroa_cast.i51, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i51, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i53 = add i64 %4, 8
  store i64 %add.i53, i64* %vsp, align 8, !tbaa !4
  %L.sroa.0.0.insert.ext.i = zext i64 %value.0.copyload.i to i128
  %R.sroa.0.0.insert.ext.i = zext i64 %value.0.copyload.i52 to i128
  %mul.i = mul nuw i128 %R.sroa.0.0.insert.ext.i, %L.sroa.0.0.insert.ext.i
  %retval.sroa.0.0.extract.trunc.i = trunc i128 %mul.i to i64
  %retval.sroa.2.0.extract.shift.i = lshr i128 %mul.i, 64
  %retval.sroa.2.0.extract.trunc.i = trunc i128 %retval.sroa.2.0.extract.shift.i to i64
  %5 = icmp ugt i128 %mul.i, 18446744073709551615
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %6 to i8
  %tobool.not.i = icmp eq i8 %conv.i.i, 0
  %conv.i26.i = zext i1 %5 to i64
  %and13.i.i = select i1 %tobool.not.i, i64 0, i64 20
  %shl34.i.i = select i1 %5, i64 2048, i64 0
  %and25.i.i = select i1 %tobool.not.i, i64 0, i64 192
  %or6.i.i = or i64 %shl34.i.i, %conv.i26.i
  %or29.i.i = or i64 %or6.i.i, %and25.i.i
  %or30.i.i = or i64 %or29.i.i, %and13.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i71 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i71 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %7 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i72 = add i64 %7, -8
  store i64 %sub.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i72
  %value.addr.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  store i64 %retval.sroa.2.0.extract.trunc.i, i64* %value.addr.0.arrayidx.sroa_cast.i74, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i75 = add i64 %8, -8
  store i64 %sub.i75, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i76 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i75
  %value.addr.0.arrayidx.sroa_cast.i77 = bitcast i8* %arrayidx.i76 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i77, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3MULIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i39 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i40 = bitcast i8* %arrayidx.i39 to i32*
  %value.0.copyload.i41 = load i32, i32* %value.0.arrayidx.sroa_cast.i40, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i42 = trunc i64 %3 to i32
  store i32 %conv.i.i42, i32* %value.0.arrayidx.sroa_cast.i40, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i43 = add i64 %4, 4
  store i64 %add.i43, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i32 %value.0.copyload.i to i64
  %conv.i44 = zext i32 %value.0.copyload.i41 to i64
  %mul.i = mul nuw i64 %conv.i44, %conv.i
  %conv.i45 = trunc i64 %mul.i to i32
  %shr.i = lshr i64 %mul.i, 32
  %conv.i46 = trunc i64 %shr.i to i32
  %5 = icmp ugt i64 %mul.i, 4294967295
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i47 = trunc i64 %6 to i8
  %tobool.not.i = icmp eq i8 %conv.i.i47, 0
  %conv.i24.i = zext i1 %5 to i64
  %and13.i.i = select i1 %tobool.not.i, i64 0, i64 20
  %shl34.i.i = select i1 %5, i64 2048, i64 0
  %and25.i.i = select i1 %tobool.not.i, i64 0, i64 192
  %or6.i.i = or i64 %shl34.i.i, %conv.i24.i
  %or29.i.i = or i64 %or6.i.i, %and25.i.i
  %or30.i.i = or i64 %or29.i.i, %and13.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i48 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i48 to i32*
  store i32 %conv.i45, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %7 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i49 = add i64 %7, -4
  store i64 %sub.i49, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i49
  %value.addr.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i32*
  store i32 %conv.i46, i32* %value.addr.0.arrayidx.sroa_cast.i51, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i52 = add i64 %8, -8
  store i64 %sub.i52, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i52
  %value.addr.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i54, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3MULItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i39 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i40 = bitcast i8* %arrayidx.i39 to i16*
  %value.0.copyload.i41 = load i16, i16* %value.0.arrayidx.sroa_cast.i40, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i42 = trunc i64 %3 to i16
  store i16 %conv.i.i42, i16* %value.0.arrayidx.sroa_cast.i40, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i43 = add i64 %4, 2
  store i64 %add.i43, i64* %vsp, align 8, !tbaa !4
  %conv.i = zext i16 %value.0.copyload.i to i32
  %conv.i44 = zext i16 %value.0.copyload.i41 to i32
  %mul.i = mul nuw i32 %conv.i44, %conv.i
  %conv.i45 = trunc i32 %mul.i to i16
  %5 = lshr i32 %mul.i, 16
  %conv2.i = trunc i32 %5 to i16
  %6 = icmp ugt i32 %mul.i, 65535
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i48 = trunc i64 %7 to i8
  %tobool.not.i = icmp eq i8 %conv.i.i48, 0
  %conv.i24.i = zext i1 %6 to i64
  %and13.i.i = select i1 %tobool.not.i, i64 0, i64 20
  %shl34.i.i = select i1 %6, i64 2048, i64 0
  %and25.i.i = select i1 %tobool.not.i, i64 0, i64 192
  %or6.i.i = or i64 %shl34.i.i, %conv.i24.i
  %or29.i.i = or i64 %or6.i.i, %and25.i.i
  %or30.i.i = or i64 %or29.i.i, %and13.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i49 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i49 to i16*
  store i16 %conv.i45, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i50 = add i64 %8, -2
  store i64 %sub.i50, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i51 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i50
  %value.addr.0.arrayidx.sroa_cast.i52 = bitcast i8* %arrayidx.i51 to i16*
  store i16 %conv2.i, i16* %value.addr.0.arrayidx.sroa_cast.i52, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i53 = add i64 %9, -8
  store i64 %sub.i53, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i54 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i53
  %value.addr.0.arrayidx.sroa_cast.i55 = bitcast i8* %arrayidx.i54 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i55, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3MULIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i32 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i33 = bitcast i8* %arrayidx.i32 to i16*
  %value.0.copyload.i34 = load i16, i16* %value.0.arrayidx.sroa_cast.i33, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i35 = trunc i64 %3 to i16
  store i16 %conv.i.i35, i16* %value.0.arrayidx.sroa_cast.i33, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i36 = add i64 %4, 2
  store i64 %add.i36, i64* %vsp, align 8, !tbaa !4
  %conv.i38 = and i16 %value.0.copyload.i, 255
  %conv.i39 = and i16 %value.0.copyload.i34, 255
  %mul.i = mul nuw i16 %conv.i39, %conv.i38
  %conv.i40 = trunc i16 %mul.i to i8
  %5 = lshr i16 %mul.i, 8
  %conv2.i = trunc i16 %5 to i8
  %6 = icmp ugt i16 %mul.i, 255
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i43 = trunc i64 %7 to i8
  %tobool.not.i = icmp eq i8 %conv.i.i43, 0
  %conv.i24.i = zext i1 %6 to i64
  %and13.i.i = select i1 %tobool.not.i, i64 0, i64 20
  %shl34.i.i = select i1 %6, i64 2048, i64 0
  %and25.i.i = select i1 %tobool.not.i, i64 0, i64 192
  %or6.i.i = or i64 %shl34.i.i, %conv.i24.i
  %or29.i.i = or i64 %or6.i.i, %and25.i.i
  %or30.i.i = or i64 %or29.i.i, %and13.i.i
  %sub.i = add i64 %4, 1
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i44 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  store i8 %conv.i40, i8* %arrayidx.i44, align 1
  %8 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i45 = add i64 %8, -1
  store i64 %sub.i45, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i46 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i45
  store i8 %conv2.i, i8* %arrayidx.i46, align 1
  %9 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i47 = add i64 %9, -8
  store i64 %sub.i47, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i48 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i47
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i48 to i64*
  store i64 %or30.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IMULImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i64*
  %value.0.copyload.i55 = load i64, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %4, 8
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %5 = ashr i64 %value.0.copyload.i, 63
  %6 = ashr i64 %value.0.copyload.i55, 63
  %L.sroa.2.0.insert.ext.i = zext i64 %5 to i128
  %L.sroa.2.0.insert.shift.i = shl nuw i128 %L.sroa.2.0.insert.ext.i, 64
  %L.sroa.0.0.insert.ext.i = zext i64 %value.0.copyload.i to i128
  %L.sroa.0.0.insert.insert.i = or i128 %L.sroa.2.0.insert.shift.i, %L.sroa.0.0.insert.ext.i
  %R.sroa.2.0.insert.ext.i = zext i64 %6 to i128
  %R.sroa.2.0.insert.shift.i = shl nuw i128 %R.sroa.2.0.insert.ext.i, 64
  %R.sroa.0.0.insert.ext.i = zext i64 %value.0.copyload.i55 to i128
  %R.sroa.0.0.insert.insert.i = or i128 %R.sroa.2.0.insert.shift.i, %R.sroa.0.0.insert.ext.i
  %mul.i = mul nsw i128 %R.sroa.0.0.insert.insert.i, %L.sroa.0.0.insert.insert.i
  %retval.sroa.0.0.extract.trunc.i = trunc i128 %mul.i to i64
  %retval.sroa.2.0.extract.shift.i = lshr i128 %mul.i, 64
  %retval.sroa.2.0.extract.trunc.i = trunc i128 %retval.sroa.2.0.extract.shift.i to i64
  %conv4.i.i.i.i = sext i64 %retval.sroa.0.0.extract.trunc.i to i128
  %cmp.i.i.i.i = icmp ne i128 %mul.i, %conv4.i.i.i.i
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %7 to i8
  %tobool.not.i.i = icmp eq i8 %conv.i.i.i, 0
  %conv.i27.i.i = zext i1 %cmp.i.i.i.i to i64
  %and13.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 20
  %shl22.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 64
  %8 = lshr i64 %retval.sroa.0.0.extract.trunc.i, 56
  %9 = and i64 %8, 128
  %shl34.i.i.i = select i1 %cmp.i.i.i.i, i64 2048, i64 0
  %and25.i.i.i = or i64 %and13.i.i.i, %9
  %or29.i.i.i = or i64 %and25.i.i.i, %shl22.i.i.i
  %or17.i.i.i = or i64 %or29.i.i.i, %conv.i27.i.i
  %or30.i.i.i = or i64 %or17.i.i.i, %shl34.i.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i74 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i74 to i64*
  store i64 %retval.sroa.0.0.extract.trunc.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i75 = add i64 %10, -8
  store i64 %sub.i75, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i76 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i75
  %value.addr.0.arrayidx.sroa_cast.i77 = bitcast i8* %arrayidx.i76 to i64*
  store i64 %retval.sroa.2.0.extract.trunc.i, i64* %value.addr.0.arrayidx.sroa_cast.i77, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i78 = add i64 %11, -8
  store i64 %sub.i78, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i79 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i78
  %value.addr.0.arrayidx.sroa_cast.i80 = bitcast i8* %arrayidx.i79 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i80, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IMULIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i40 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i41 = bitcast i8* %arrayidx.i40 to i32*
  %value.0.copyload.i42 = load i32, i32* %value.0.arrayidx.sroa_cast.i41, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i43 = trunc i64 %3 to i32
  store i32 %conv.i.i43, i32* %value.0.arrayidx.sroa_cast.i41, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i44 = add i64 %4, 4
  store i64 %add.i44, i64* %vsp, align 8, !tbaa !4
  %conv.i = sext i32 %value.0.copyload.i to i64
  %conv.i45 = sext i32 %value.0.copyload.i42 to i64
  %mul.i = mul nsw i64 %conv.i45, %conv.i
  %conv.i46 = trunc i64 %mul.i to i32
  %shr.i = lshr i64 %mul.i, 32
  %conv.i47 = trunc i64 %shr.i to i32
  %5 = add nsw i64 %mul.i, 2147483648
  %6 = icmp ugt i64 %5, 4294967295
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %7 to i8
  %tobool.not.i.i = icmp eq i8 %conv.i.i.i, 0
  %conv.i24.i.i = zext i1 %6 to i64
  %and13.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 20
  %shl22.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 64
  %8 = lshr i64 %mul.i, 24
  %9 = and i64 %8, 128
  %shl34.i.i.i = select i1 %6, i64 2048, i64 0
  %and25.i.i.i = or i64 %9, %conv.i24.i.i
  %or29.i.i.i = or i64 %and25.i.i.i, %shl34.i.i.i
  %or17.i.i.i = or i64 %or29.i.i.i, %and13.i.i.i
  %or30.i.i.i = or i64 %or17.i.i.i, %shl22.i.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i48 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i48 to i32*
  store i32 %conv.i46, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %10 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i49 = add i64 %10, -4
  store i64 %sub.i49, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i49
  %value.addr.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i32*
  store i32 %conv.i47, i32* %value.addr.0.arrayidx.sroa_cast.i51, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i52 = add i64 %11, -8
  store i64 %sub.i52, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i52
  %value.addr.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i54, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IMULItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i40 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i41 = bitcast i8* %arrayidx.i40 to i16*
  %value.0.copyload.i42 = load i16, i16* %value.0.arrayidx.sroa_cast.i41, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i43 = trunc i64 %3 to i16
  store i16 %conv.i.i43, i16* %value.0.arrayidx.sroa_cast.i41, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i44 = add i64 %4, 2
  store i64 %add.i44, i64* %vsp, align 8, !tbaa !4
  %conv.i = sext i16 %value.0.copyload.i to i32
  %conv.i45 = sext i16 %value.0.copyload.i42 to i32
  %mul.i = mul nsw i32 %conv.i45, %conv.i
  %conv.i46 = trunc i32 %mul.i to i16
  %5 = lshr i32 %mul.i, 16
  %conv2.i = trunc i32 %5 to i16
  %6 = add nsw i32 %mul.i, 32768
  %7 = icmp ugt i32 %6, 65535
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %8 to i8
  %tobool.not.i.i = icmp eq i8 %conv.i.i.i, 0
  %conv.i24.i.i = zext i1 %7 to i64
  %and13.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 20
  %shl22.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 64
  %9 = lshr i16 %conv.i46, 8
  %10 = and i16 %9, 128
  %11 = zext i16 %10 to i64
  %shl34.i.i.i = select i1 %7, i64 2048, i64 0
  %and25.i.i.i = or i64 %shl34.i.i.i, %conv.i24.i.i
  %or29.i.i.i = or i64 %and25.i.i.i, %11
  %or17.i.i.i = or i64 %or29.i.i.i, %and13.i.i.i
  %or30.i.i.i = or i64 %or17.i.i.i, %shl22.i.i.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i49 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i49 to i16*
  store i16 %conv.i46, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i50 = add i64 %12, -2
  store i64 %sub.i50, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i51 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i50
  %value.addr.0.arrayidx.sroa_cast.i52 = bitcast i8* %arrayidx.i51 to i16*
  store i16 %conv2.i, i16* %value.addr.0.arrayidx.sroa_cast.i52, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i53 = add i64 %13, -8
  store i64 %sub.i53, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i54 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i53
  %value.addr.0.arrayidx.sroa_cast.i55 = bitcast i8* %arrayidx.i54 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i55, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4IMULIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i34 = bitcast i8* %arrayidx.i33 to i16*
  %value.0.copyload.i35 = load i16, i16* %value.0.arrayidx.sroa_cast.i34, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i36 = trunc i64 %3 to i16
  store i16 %conv.i.i36, i16* %value.0.arrayidx.sroa_cast.i34, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i37 = add i64 %4, 2
  store i64 %add.i37, i64* %vsp, align 8, !tbaa !4
  %sext = shl i16 %value.0.copyload.i, 8
  %conv.i39 = ashr exact i16 %sext, 8
  %sext51 = shl i16 %value.0.copyload.i35, 8
  %conv.i40 = ashr exact i16 %sext51, 8
  %mul.i = mul nsw i16 %conv.i40, %conv.i39
  %conv.i41 = trunc i16 %mul.i to i8
  %5 = lshr i16 %mul.i, 8
  %conv2.i = trunc i16 %5 to i8
  %6 = add nsw i16 %mul.i, 128
  %7 = icmp ugt i16 %6, 255
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i.i = trunc i64 %8 to i8
  %tobool.not.i.i = icmp eq i8 %conv.i.i.i, 0
  %conv.i24.i.i = zext i1 %7 to i64
  %and13.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 20
  %shl22.i.i.i = select i1 %tobool.not.i.i, i64 0, i64 64
  %9 = and i8 %conv.i41, -128
  %10 = zext i8 %9 to i64
  %shl34.i.i.i = select i1 %7, i64 2048, i64 0
  %and25.i.i.i = or i64 %10, %conv.i24.i.i
  %or29.i.i.i = or i64 %and25.i.i.i, %shl34.i.i.i
  %or17.i.i.i = or i64 %or29.i.i.i, %and13.i.i.i
  %or30.i.i.i = or i64 %or17.i.i.i, %shl22.i.i.i
  %sub.i = add i64 %4, 1
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i44 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  store i8 %conv.i41, i8* %arrayidx.i44, align 1
  %11 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i45 = add i64 %11, -1
  store i64 %sub.i45, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i46 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i45
  store i8 %conv2.i, i8* %arrayidx.i46, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i47 = add i64 %12, -8
  store i64 %sub.i47, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i48 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i47
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i48 to i64*
  store i64 %or30.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3NORImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i64*
  %value.0.copyload.i31 = load i64, i64* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %or.i = or i64 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i64 %or.i, -1
  %conv.i.i.i = trunc i64 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %cmp.i.i.i = icmp eq i64 %or.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i = select i1 %cmp.i.i.i, i64 64, i64 0
  %10 = lshr i64 %neg.i, 56
  %11 = and i64 %10, 128
  %or17.i.i = or i64 %11, %shl22.i.i
  %and25.i.i = or i64 %or17.i.i, %9
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i33 to i64*
  store i64 %neg.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i34 = add i64 %12, -8
  store i64 %sub.i34, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i35 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i34
  %value.addr.0.arrayidx.sroa_cast.i36 = bitcast i8* %arrayidx.i35 to i64*
  store i64 %and25.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i36, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3NORIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i32*
  %value.0.copyload.i31 = load i32, i32* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i32 = trunc i64 %3 to i32
  store i32 %conv.i.i32, i32* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %or3.i = or i32 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i32 %or3.i, -1
  %conv.i.i.i = trunc i32 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %cmp.i.i.i = icmp eq i32 %or3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i = select i1 %cmp.i.i.i, i64 64, i64 0
  %10 = lshr i32 %neg.i, 24
  %11 = and i32 %10, 128
  %12 = zext i32 %11 to i64
  %or17.i.i = or i64 %shl22.i.i, %12
  %and25.i.i = or i64 %or17.i.i, %9
  %arrayidx.i34 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i34 to i32*
  store i32 %neg.i, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i35 = add i64 %13, -8
  store i64 %sub.i35, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i36 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i35
  %value.addr.0.arrayidx.sroa_cast.i37 = bitcast i8* %arrayidx.i36 to i64*
  store i64 %and25.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i37, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3NORItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i16*
  %value.0.copyload.i31 = load i16, i16* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i32 = trunc i64 %3 to i16
  store i16 %conv.i.i32, i16* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %or3.i = or i16 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i16 %or3.i, -1
  %conv.i.i.i = trunc i16 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i) #3, !range !10
  %cmp.i.i.i = icmp eq i16 %or3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i = select i1 %cmp.i.i.i, i64 64, i64 0
  %10 = lshr i16 %neg.i, 8
  %11 = and i16 %10, 128
  %12 = zext i16 %11 to i64
  %or17.i.i = or i64 %shl22.i.i, %12
  %and25.i.i = or i64 %or17.i.i, %9
  %arrayidx.i34 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i34 to i16*
  store i16 %neg.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i35 = add i64 %13, -8
  store i64 %sub.i35, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i36 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i35
  %value.addr.0.arrayidx.sroa_cast.i37 = bitcast i8* %arrayidx.i36 to i64*
  store i64 %and25.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i37, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3NORIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i24 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i25 = bitcast i8* %arrayidx.i24 to i16*
  %value.0.copyload.i26 = load i16, i16* %value.0.arrayidx.sroa_cast.i25, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i27 = trunc i64 %3 to i16
  store i16 %conv.i.i27, i16* %value.0.arrayidx.sroa_cast.i25, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %or3.i37 = or i16 %value.0.copyload.i26, %value.0.copyload.i
  %or3.i = trunc i16 %or3.i37 to i8
  %neg.i = xor i8 %or3.i, -1
  %5 = tail call i8 @llvm.ctpop.i8(i8 %neg.i) #3, !range !10
  %cmp.i.i.i = icmp eq i8 %or3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i = select i1 %cmp.i.i.i, i64 64, i64 0
  %10 = and i8 %neg.i, -128
  %11 = zext i8 %10 to i64
  %or17.i.i = or i64 %shl22.i.i, %11
  %and25.i.i = or i64 %or17.i.i, %9
  %conv.i30 = zext i8 %neg.i to i16
  %arrayidx.i31 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i31 to i16*
  store i16 %conv.i30, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i32 = add i64 %12, -8
  store i64 %sub.i32, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i32
  %value.addr.0.arrayidx.sroa_cast.i34 = bitcast i8* %arrayidx.i33 to i64*
  store i64 %and25.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i34, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4NANDImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i64*
  %value.0.copyload.i31 = load i64, i64* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %and.i = and i64 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i64 %and.i, -1
  %conv.i.i.i.i = trunc i64 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i.i) #3, !range !10
  %cmp.i.i.i.i = icmp eq i64 %and.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i.i = select i1 %cmp.i.i.i.i, i64 64, i64 0
  %10 = lshr i64 %neg.i, 56
  %11 = and i64 %10, 128
  %or17.i.i.i = or i64 %11, %shl22.i.i.i
  %and25.i.i.i = or i64 %or17.i.i.i, %9
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i33 to i64*
  store i64 %neg.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i34 = add i64 %12, -8
  store i64 %sub.i34, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i35 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i34
  %value.addr.0.arrayidx.sroa_cast.i36 = bitcast i8* %arrayidx.i35 to i64*
  store i64 %and25.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i36, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4NANDIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i32*
  %value.0.copyload.i31 = load i32, i32* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i32 = trunc i64 %3 to i32
  store i32 %conv.i.i32, i32* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %and3.i = and i32 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i32 %and3.i, -1
  %conv.i.i.i.i = trunc i32 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i.i) #3, !range !10
  %cmp.i.i.i.i = icmp eq i32 %and3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i.i = select i1 %cmp.i.i.i.i, i64 64, i64 0
  %10 = lshr i32 %neg.i, 24
  %11 = and i32 %10, 128
  %12 = zext i32 %11 to i64
  %or17.i.i.i = or i64 %shl22.i.i.i, %12
  %and25.i.i.i = or i64 %or17.i.i.i, %9
  %arrayidx.i34 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i34 to i32*
  store i32 %neg.i, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i35 = add i64 %13, -8
  store i64 %sub.i35, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i36 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i35
  %value.addr.0.arrayidx.sroa_cast.i37 = bitcast i8* %arrayidx.i36 to i64*
  store i64 %and25.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i37, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4NANDItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i29 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i30 = bitcast i8* %arrayidx.i29 to i16*
  %value.0.copyload.i31 = load i16, i16* %value.0.arrayidx.sroa_cast.i30, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i32 = trunc i64 %3 to i16
  store i16 %conv.i.i32, i16* %value.0.arrayidx.sroa_cast.i30, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %and3.i = and i16 %value.0.copyload.i31, %value.0.copyload.i
  %neg.i = xor i16 %and3.i, -1
  %conv.i.i.i.i = trunc i16 %neg.i to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i.i.i) #3, !range !10
  %cmp.i.i.i.i = icmp eq i16 %and3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i.i = select i1 %cmp.i.i.i.i, i64 64, i64 0
  %10 = lshr i16 %neg.i, 8
  %11 = and i16 %10, 128
  %12 = zext i16 %11 to i64
  %or17.i.i.i = or i64 %shl22.i.i.i, %12
  %and25.i.i.i = or i64 %or17.i.i.i, %9
  %arrayidx.i34 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i34 to i16*
  store i16 %neg.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i35 = add i64 %13, -8
  store i64 %sub.i35, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i36 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i35
  %value.addr.0.arrayidx.sroa_cast.i37 = bitcast i8* %arrayidx.i36 to i64*
  store i64 %and25.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i37, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4NANDIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i24 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i25 = bitcast i8* %arrayidx.i24 to i16*
  %value.0.copyload.i26 = load i16, i16* %value.0.arrayidx.sroa_cast.i25, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i27 = trunc i64 %3 to i16
  store i16 %conv.i.i27, i16* %value.0.arrayidx.sroa_cast.i25, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %and3.i37 = and i16 %value.0.copyload.i26, %value.0.copyload.i
  %and3.i = trunc i16 %and3.i37 to i8
  %neg.i = xor i8 %and3.i, -1
  %5 = tail call i8 @llvm.ctpop.i8(i8 %neg.i) #3, !range !10
  %cmp.i.i.i.i = icmp eq i8 %and3.i, -1
  %6 = shl nuw nsw i8 %5, 2
  %7 = and i8 %6, 4
  %8 = xor i8 %7, 4
  %9 = zext i8 %8 to i64
  %shl22.i.i.i = select i1 %cmp.i.i.i.i, i64 64, i64 0
  %10 = and i8 %neg.i, -128
  %11 = zext i8 %10 to i64
  %or17.i.i.i = or i64 %shl22.i.i.i, %11
  %and25.i.i.i = or i64 %or17.i.i.i, %9
  %conv.i30 = zext i8 %neg.i to i16
  %arrayidx.i31 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i31 to i16*
  store i16 %conv.i30, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %12 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i32 = add i64 %12, -8
  store i64 %sub.i32, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i33 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i32
  %value.addr.0.arrayidx.sroa_cast.i34 = bitcast i8* %arrayidx.i33 to i64*
  store i64 %and25.i.i.i, i64* %value.addr.0.arrayidx.sroa_cast.i34, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHLImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i51 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i52 = bitcast i8* %arrayidx.i51 to i16*
  %value.0.copyload.i53 = load i16, i16* %value.0.arrayidx.sroa_cast.i52, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %3 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i52, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i54 = add i64 %4, 2
  store i64 %add.i54, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i53 to i64
  %shl = shl i64 %value.0.copyload.i, %conv7
  %and.i.i = and i64 %conv7, 63
  %cmp.i.i = icmp eq i64 %and.i.i, 1
  %cmp.i.i.i = icmp slt i64 %value.0.copyload.i, 0
  %cmp.i.i24.i = icmp slt i64 %shl, 0
  %retval.0.i = select i1 %cmp.i.i, i1 %cmp.i.i.i, i1 %cmp.i.i24.i
  %conv.i.i55 = trunc i64 %shl to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i55) #3, !range !10
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %6 to i8
  %tobool12.not = icmp eq i8 %conv.i, 0
  %cmp.i.i56 = icmp eq i64 %shl, 0
  %7 = xor i64 %shl, %value.0.copyload.i
  %conv.i58 = zext i1 %retval.0.i to i64
  %8 = shl nuw nsw i8 %5, 2
  %9 = and i8 %8, 4
  %10 = xor i8 %9, 4
  %11 = zext i8 %10 to i64
  %shl16.i = select i1 %tobool12.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i56, i64 64, i64 0
  %12 = lshr i64 %shl, 56
  %13 = and i64 %12, 128
  %14 = lshr i64 %7, 52
  %15 = and i64 %14, 2048
  %and13.i = or i64 %13, %shl22.i
  %or17.i = or i64 %and13.i, %15
  %and25.i = or i64 %or17.i, %conv.i58
  %or29.i = or i64 %and25.i, %11
  %or30.i = or i64 %or29.i, %shl16.i
  %sub.i = add i64 %4, -6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i59 to i64*
  store i64 %shl, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %16 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i60 = add i64 %16, -8
  store i64 %sub.i60, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i61 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i60
  %value.addr.0.arrayidx.sroa_cast.i62 = bitcast i8* %arrayidx.i61 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i62, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHLIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i51 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i52 = bitcast i8* %arrayidx.i51 to i16*
  %value.0.copyload.i53 = load i16, i16* %value.0.arrayidx.sroa_cast.i52, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i54 = trunc i64 %3 to i16
  store i16 %conv.i.i54, i16* %value.0.arrayidx.sroa_cast.i52, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i55 = add i64 %4, 2
  store i64 %add.i55, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i53 to i32
  %shl = shl i32 %value.0.copyload.i, %conv7
  %and3.i.i = and i32 %conv7, 31
  %cmp.i.i = icmp eq i32 %and3.i.i, 1
  %cmp.i.i.i = icmp slt i32 %value.0.copyload.i, 0
  %cmp.i.i24.i = icmp slt i32 %shl, 0
  %retval.0.i = select i1 %cmp.i.i, i1 %cmp.i.i.i, i1 %cmp.i.i24.i
  %conv.i.i56 = trunc i32 %shl to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i56) #3, !range !10
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %6 to i8
  %tobool12.not = icmp eq i8 %conv.i, 0
  %cmp.i.i57 = icmp eq i32 %shl, 0
  %7 = xor i32 %shl, %value.0.copyload.i
  %conv.i59 = zext i1 %retval.0.i to i64
  %8 = shl nuw nsw i8 %5, 2
  %9 = and i8 %8, 4
  %10 = xor i8 %9, 4
  %11 = zext i8 %10 to i64
  %shl16.i = select i1 %tobool12.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i57, i64 64, i64 0
  %12 = lshr i32 %shl, 24
  %13 = and i32 %12, 128
  %14 = zext i32 %13 to i64
  %15 = lshr i32 %7, 20
  %16 = and i32 %15, 2048
  %17 = zext i32 %16 to i64
  %and13.i = or i64 %shl22.i, %14
  %or17.i = or i64 %and13.i, %conv.i59
  %and25.i = or i64 %or17.i, %17
  %or29.i = or i64 %and25.i, %11
  %or30.i = or i64 %or29.i, %shl16.i
  %sub.i = add i64 %4, -2
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i60 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i60 to i32*
  store i32 %shl, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %18 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i61 = add i64 %18, -8
  store i64 %sub.i61, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i62 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i61
  %value.addr.0.arrayidx.sroa_cast.i63 = bitcast i8* %arrayidx.i62 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i63, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHLItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i55 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i56 = bitcast i8* %arrayidx.i55 to i16*
  %value.0.copyload.i57 = load i16, i16* %value.0.arrayidx.sroa_cast.i56, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i58 = trunc i64 %3 to i16
  store i16 %conv.i.i58, i16* %value.0.arrayidx.sroa_cast.i56, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i59 = add i64 %4, 2
  store i64 %add.i59, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i to i32
  %conv8 = zext i16 %value.0.copyload.i57 to i32
  %shl = shl i32 %conv7, %conv8
  %conv9 = trunc i32 %shl to i16
  %and3.i.i = and i16 %value.0.copyload.i57, 31
  %cmp.i.i = icmp eq i16 %and3.i.i, 1
  br i1 %cmp.i.i, label %if.then.i, label %if.else.i

if.then.i:                                        ; preds = %entry
  %cmp.i.i.i = icmp slt i16 %value.0.copyload.i, 0
  br label %_Z6CF_SHLItEbT_S0_S0_.exit

if.else.i:                                        ; preds = %entry
  %cmp.i23.i = icmp ult i16 %and3.i.i, 16
  br i1 %cmp.i23.i, label %if.then7.i, label %if.end9.i

if.then7.i:                                       ; preds = %if.else.i
  %cmp.i.i24.i = icmp slt i16 %conv9, 0
  br label %_Z6CF_SHLItEbT_S0_S0_.exit

if.end9.i:                                        ; preds = %if.else.i
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i60 = trunc i64 %5 to i8
  %tobool.i = icmp ne i8 %conv.i.i60, 0
  br label %_Z6CF_SHLItEbT_S0_S0_.exit

_Z6CF_SHLItEbT_S0_S0_.exit:                       ; preds = %if.then.i, %if.then7.i, %if.end9.i
  %retval.0.i = phi i1 [ %cmp.i.i.i, %if.then.i ], [ %cmp.i.i24.i, %if.then7.i ], [ %tobool.i, %if.end9.i ]
  %conv.i.i61 = trunc i32 %shl to i8
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i61) #3, !range !10
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %7 to i8
  %tobool14.not = icmp eq i8 %conv.i, 0
  %cmp.i.i62 = icmp eq i32 %shl, 0
  %8 = xor i16 %value.0.copyload.i, %conv9
  %conv.i64 = zext i1 %retval.0.i to i64
  %9 = shl nuw nsw i8 %6, 2
  %10 = and i8 %9, 4
  %11 = xor i8 %10, 4
  %12 = zext i8 %11 to i64
  %shl16.i = select i1 %tobool14.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i62, i64 64, i64 0
  %13 = lshr i32 %shl, 24
  %14 = and i32 %13, 128
  %15 = zext i32 %14 to i64
  %16 = lshr i16 %8, 4
  %17 = and i16 %16, 2048
  %18 = zext i16 %17 to i64
  %and13.i = or i64 %shl22.i, %15
  %or17.i = or i64 %and13.i, %18
  %and25.i = or i64 %or17.i, %12
  %or29.i = or i64 %and25.i, %conv.i64
  %or30.i = or i64 %or29.i, %shl16.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i65 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i65 to i16*
  store i16 %conv9, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %19 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i66 = add i64 %19, -8
  store i64 %sub.i66, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i67 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i66
  %value.addr.0.arrayidx.sroa_cast.i68 = bitcast i8* %arrayidx.i67 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i68, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHLIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %conv.i = trunc i16 %value.0.copyload.i to i8
  %arrayidx.i52 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i53 = bitcast i8* %arrayidx.i52 to i16*
  %value.0.copyload.i54 = load i16, i16* %value.0.arrayidx.sroa_cast.i53, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i55 = trunc i64 %3 to i16
  store i16 %conv.i.i55, i16* %value.0.arrayidx.sroa_cast.i53, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %4, 2
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %conv.i57 = trunc i16 %value.0.copyload.i54 to i8
  %conv.i.mask = and i16 %value.0.copyload.i, 255
  %conv6 = zext i16 %conv.i.mask to i32
  %conv.i57.mask = and i16 %value.0.copyload.i54, 255
  %conv7 = zext i16 %conv.i57.mask to i32
  %shl = shl i32 %conv6, %conv7
  %conv8 = trunc i32 %shl to i8
  %and3.i.i = and i8 %conv.i57, 31
  %cmp.i.i = icmp eq i8 %and3.i.i, 1
  br i1 %cmp.i.i, label %if.then.i, label %if.else.i

if.then.i:                                        ; preds = %entry
  %cmp.i.i.i = icmp slt i8 %conv.i, 0
  br label %_Z6CF_SHLIhEbT_S0_S0_.exit

if.else.i:                                        ; preds = %entry
  %cmp.i18.i = icmp ult i8 %and3.i.i, 8
  br i1 %cmp.i18.i, label %if.then7.i, label %if.end9.i

if.then7.i:                                       ; preds = %if.else.i
  %cmp.i.i19.i = icmp slt i8 %conv8, 0
  br label %_Z6CF_SHLIhEbT_S0_S0_.exit

if.end9.i:                                        ; preds = %if.else.i
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i58 = trunc i64 %5 to i8
  %tobool.i = icmp ne i8 %conv.i.i58, 0
  br label %_Z6CF_SHLIhEbT_S0_S0_.exit

_Z6CF_SHLIhEbT_S0_S0_.exit:                       ; preds = %if.then.i, %if.then7.i, %if.end9.i
  %retval.0.i = phi i1 [ %cmp.i.i.i, %if.then.i ], [ %cmp.i.i19.i, %if.then7.i ], [ %tobool.i, %if.end9.i ]
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv8) #3, !range !10
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i60 = trunc i64 %7 to i8
  %tobool13.not = icmp eq i8 %conv.i60, 0
  %cmp.i.i61 = icmp eq i32 %shl, 0
  %8 = xor i8 %conv8, %conv.i
  %conv.i63 = zext i1 %retval.0.i to i64
  %9 = shl nuw nsw i8 %6, 2
  %10 = and i8 %9, 4
  %11 = xor i8 %10, 4
  %12 = zext i8 %11 to i64
  %shl16.i = select i1 %tobool13.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i61, i64 64, i64 0
  %13 = lshr i32 %shl, 24
  %14 = and i32 %13, 128
  %15 = zext i32 %14 to i64
  %16 = and i8 %8, -128
  %17 = zext i8 %16 to i64
  %18 = shl nuw nsw i64 %17, 4
  %and25.i = or i64 %shl22.i, %15
  %and13.i = or i64 %18, %and25.i
  %or17.i = or i64 %and13.i, %12
  %or29.i = or i64 %or17.i, %conv.i63
  %or30.i = or i64 %or29.i, %shl16.i
  %conv.i64 = trunc i32 %shl to i16
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i65 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i65 to i16*
  store i16 %conv.i64, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %19 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i66 = add i64 %19, -8
  store i64 %sub.i66, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i67 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i66
  %value.addr.0.arrayidx.sroa_cast.i68 = bitcast i8* %arrayidx.i67 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i68, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHRImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i16*
  %value.0.copyload.i49 = load i16, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %3 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i50 = add i64 %4, 2
  store i64 %add.i50, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i49 to i64
  %shr = lshr i64 %value.0.copyload.i, %conv7
  %and.i.i = and i64 %conv7, 63
  %cmp.i.i = icmp eq i64 %and.i.i, 1
  %and.i25.i = and i64 %value.0.copyload.i, 1
  %cmp.i26.i = icmp ne i64 %and.i25.i, 0
  %and.i28.i = and i64 %shr, 1
  %cmp.i29.i = icmp ne i64 %and.i28.i, 0
  %retval.0.i = select i1 %cmp.i.i, i1 %cmp.i26.i, i1 %cmp.i29.i
  %conv.i.i51 = trunc i64 %shr to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i51) #3, !range !10
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %6 to i8
  %tobool12.not = icmp eq i8 %conv.i, 0
  %cmp.i.i52 = icmp eq i64 %shr, 0
  %conv.i53 = zext i1 %retval.0.i to i64
  %7 = shl nuw nsw i8 %5, 2
  %8 = and i8 %7, 4
  %9 = xor i8 %8, 4
  %10 = zext i8 %9 to i64
  %shl16.i = select i1 %tobool12.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i52, i64 64, i64 0
  %11 = lshr i64 %value.0.copyload.i, 52
  %12 = and i64 %11, 2048
  %and13.i = or i64 %shl22.i, %12
  %or17.i = or i64 %and13.i, %conv.i53
  %or29.i = or i64 %or17.i, %10
  %or30.i = or i64 %or29.i, %shl16.i
  %sub.i = add i64 %4, -6
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i54 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i54 to i64*
  store i64 %shr, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %13 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i55 = add i64 %13, -8
  store i64 %sub.i55, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i56 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i55
  %value.addr.0.arrayidx.sroa_cast.i57 = bitcast i8* %arrayidx.i56 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i57, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHRIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i16*
  %value.0.copyload.i49 = load i16, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i50 = trunc i64 %3 to i16
  store i16 %conv.i.i50, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i51 = add i64 %4, 2
  store i64 %add.i51, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i49 to i32
  %shr = lshr i32 %value.0.copyload.i, %conv7
  %and3.i.i = and i32 %conv7, 31
  %cmp.i.i = icmp eq i32 %and3.i.i, 1
  %and3.i25.i = and i32 %value.0.copyload.i, 1
  %cmp.i26.i = icmp ne i32 %and3.i25.i, 0
  %and3.i28.i = and i32 %shr, 1
  %cmp.i29.i = icmp ne i32 %and3.i28.i, 0
  %retval.0.i = select i1 %cmp.i.i, i1 %cmp.i26.i, i1 %cmp.i29.i
  %conv.i.i52 = trunc i32 %shr to i8
  %5 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i52) #3, !range !10
  %6 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %6 to i8
  %tobool12.not = icmp eq i8 %conv.i, 0
  %cmp.i.i53 = icmp eq i32 %shr, 0
  %conv.i54 = zext i1 %retval.0.i to i64
  %7 = shl nuw nsw i8 %5, 2
  %8 = and i8 %7, 4
  %9 = xor i8 %8, 4
  %10 = zext i8 %9 to i64
  %shl16.i = select i1 %tobool12.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i53, i64 64, i64 0
  %11 = lshr i32 %value.0.copyload.i, 20
  %12 = and i32 %11, 2048
  %13 = zext i32 %12 to i64
  %and13.i = or i64 %shl22.i, %13
  %or17.i = or i64 %and13.i, %conv.i54
  %or29.i = or i64 %or17.i, %10
  %or30.i = or i64 %or29.i, %shl16.i
  %sub.i = add i64 %4, -2
  store i64 %sub.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i55 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i55 to i32*
  store i32 %shr, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %14 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i56 = add i64 %14, -8
  store i64 %sub.i56, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i56
  %value.addr.0.arrayidx.sroa_cast.i58 = bitcast i8* %arrayidx.i57 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i58, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHRItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i50 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i51 = bitcast i8* %arrayidx.i50 to i16*
  %value.0.copyload.i52 = load i16, i16* %value.0.arrayidx.sroa_cast.i51, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i53 = trunc i64 %3 to i16
  store i16 %conv.i.i53, i16* %value.0.arrayidx.sroa_cast.i51, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i54 = add i64 %4, 2
  store i64 %add.i54, i64* %vsp, align 8, !tbaa !4
  %conv7 = zext i16 %value.0.copyload.i to i32
  %conv8 = zext i16 %value.0.copyload.i52 to i32
  %shr = lshr i32 %conv7, %conv8
  %conv9 = trunc i32 %shr to i16
  %and3.i.i = and i16 %value.0.copyload.i52, 31
  %cmp.i.i = icmp eq i16 %and3.i.i, 1
  br i1 %cmp.i.i, label %if.then.i, label %if.else.i

if.then.i:                                        ; preds = %entry
  %and3.i25.i = and i16 %value.0.copyload.i, 1
  %cmp.i26.i = icmp ne i16 %and3.i25.i, 0
  br label %_Z6CF_SHRItEbT_S0_S0_.exit

if.else.i:                                        ; preds = %entry
  %cmp.i27.i = icmp ult i16 %and3.i.i, 16
  br i1 %cmp.i27.i, label %if.then8.i, label %if.end11.i

if.then8.i:                                       ; preds = %if.else.i
  %and3.i28.i = and i16 %conv9, 1
  %cmp.i29.i = icmp ne i16 %and3.i28.i, 0
  br label %_Z6CF_SHRItEbT_S0_S0_.exit

if.end11.i:                                       ; preds = %if.else.i
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i55 = trunc i64 %5 to i8
  %tobool.i = icmp ne i8 %conv.i.i55, 0
  br label %_Z6CF_SHRItEbT_S0_S0_.exit

_Z6CF_SHRItEbT_S0_S0_.exit:                       ; preds = %if.then.i, %if.then8.i, %if.end11.i
  %retval.0.i = phi i1 [ %cmp.i26.i, %if.then.i ], [ %cmp.i29.i, %if.then8.i ], [ %tobool.i, %if.end11.i ]
  %conv.i.i56 = trunc i32 %shr to i8
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i56) #3, !range !10
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %7 to i8
  %tobool14.not = icmp eq i8 %conv.i, 0
  %cmp.i.i57 = icmp eq i32 %shr, 0
  %conv.i58 = zext i1 %retval.0.i to i64
  %8 = shl nuw nsw i8 %6, 2
  %9 = and i8 %8, 4
  %10 = xor i8 %9, 4
  %11 = zext i8 %10 to i64
  %shl16.i = select i1 %tobool14.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i57, i64 64, i64 0
  %12 = lshr i16 %value.0.copyload.i, 4
  %13 = and i16 %12, 2048
  %14 = zext i16 %13 to i64
  %and13.i = or i64 %shl22.i, %14
  %or17.i = or i64 %and13.i, %11
  %or29.i = or i64 %or17.i, %conv.i58
  %or30.i = or i64 %or29.i, %shl16.i
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i59 to i16*
  store i16 %conv9, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %15 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i60 = add i64 %15, -8
  store i64 %sub.i60, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i61 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i60
  %value.addr.0.arrayidx.sroa_cast.i62 = bitcast i8* %arrayidx.i61 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i62, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z3SHRIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i47 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i48 = bitcast i8* %arrayidx.i47 to i16*
  %value.0.copyload.i49 = load i16, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i50 = trunc i64 %3 to i16
  store i16 %conv.i.i50, i16* %value.0.arrayidx.sroa_cast.i48, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i51 = add i64 %4, 2
  store i64 %add.i51, i64* %vsp, align 8, !tbaa !4
  %conv.i52 = trunc i16 %value.0.copyload.i49 to i8
  %conv.i.mask = and i16 %value.0.copyload.i, 255
  %conv6 = zext i16 %conv.i.mask to i32
  %conv.i52.mask = and i16 %value.0.copyload.i49, 255
  %conv7 = zext i16 %conv.i52.mask to i32
  %shr = lshr i32 %conv6, %conv7
  %conv8 = trunc i32 %shr to i8
  %and3.i.i = and i8 %conv.i52, 31
  %cmp.i.i = icmp eq i8 %and3.i.i, 1
  br i1 %cmp.i.i, label %if.then.i, label %if.else.i

if.then.i:                                        ; preds = %entry
  %conv.i = trunc i16 %value.0.copyload.i to i8
  %and3.i20.i = and i8 %conv.i, 1
  br label %_Z6CF_SHRIhEbT_S0_S0_.exit

if.else.i:                                        ; preds = %entry
  %cmp.i22.i = icmp ult i8 %and3.i.i, 8
  br i1 %cmp.i22.i, label %if.then8.i, label %if.end11.i

if.then8.i:                                       ; preds = %if.else.i
  %and3.i23.i = and i8 %conv8, 1
  br label %_Z6CF_SHRIhEbT_S0_S0_.exit

if.end11.i:                                       ; preds = %if.else.i
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i53 = trunc i64 %5 to i8
  br label %_Z6CF_SHRIhEbT_S0_S0_.exit

_Z6CF_SHRIhEbT_S0_S0_.exit:                       ; preds = %if.then.i, %if.then8.i, %if.end11.i
  %retval.0.in.i = phi i8 [ %and3.i20.i, %if.then.i ], [ %and3.i23.i, %if.then8.i ], [ %conv.i.i53, %if.end11.i ]
  %retval.0.i = icmp ne i8 %retval.0.in.i, 0
  %6 = tail call i8 @llvm.ctpop.i8(i8 %conv8) #3, !range !10
  %7 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i55 = trunc i64 %7 to i8
  %tobool13.not = icmp eq i8 %conv.i55, 0
  %cmp.i.i56 = icmp eq i32 %shr, 0
  %conv.i57 = zext i1 %retval.0.i to i64
  %8 = shl nuw nsw i8 %6, 2
  %9 = and i8 %8, 4
  %10 = xor i8 %9, 4
  %11 = zext i8 %10 to i64
  %shl16.i = select i1 %tobool13.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i56, i64 64, i64 0
  %12 = shl i16 %value.0.copyload.i, 4
  %13 = and i16 %12, 2048
  %14 = zext i16 %13 to i64
  %and13.i = or i64 %shl22.i, %14
  %or17.i = or i64 %and13.i, %11
  %or29.i = or i64 %or17.i, %conv.i57
  %or30.i = or i64 %or29.i, %shl16.i
  %conv.i58 = trunc i32 %shr to i16
  store i64 %4, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %4
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i59 to i16*
  store i16 %conv.i58, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %15 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i60 = add i64 %15, -8
  store i64 %sub.i60, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i61 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i60
  %value.addr.0.arrayidx.sroa_cast.i62 = bitcast i8* %arrayidx.i61 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i62, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHLDImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i64*
  %value.0.copyload.i55 = load i64, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %4, 8
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i56
  %value.0.arrayidx.sroa_cast.i58 = bitcast i8* %arrayidx.i57 to i16*
  %value.0.copyload.i59 = load i16, i16* %value.0.arrayidx.sroa_cast.i58, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %5 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i58, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i60 = add i64 %6, 2
  store i64 %add.i60, i64* %vsp, align 8, !tbaa !4
  %7 = and i16 %value.0.copyload.i59, 63
  %and.i = zext i16 %7 to i64
  %shl.i = shl i64 %value.0.copyload.i, %and.i
  %sub.i = sub nuw nsw i64 64, %and.i
  %shr.i = lshr i64 %value.0.copyload.i55, %sub.i
  %or.i = or i64 %shr.i, %shl.i
  %conv.i.i61 = trunc i64 %or.i to i8
  %8 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i61) #3, !range !10
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %9 to i8
  %tobool.not = icmp eq i8 %conv.i, 0
  %cmp.i.i = icmp eq i64 %or.i, 0
  %10 = xor i64 %or.i, %value.0.copyload.i
  %11 = lshr i64 %value.0.copyload.i, %sub.i
  %12 = and i64 %11, 1
  %13 = shl nuw nsw i8 %8, 2
  %14 = and i8 %13, 4
  %15 = xor i8 %14, 4
  %16 = zext i8 %15 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %17 = lshr i64 %or.i, 56
  %18 = and i64 %17, 128
  %19 = lshr i64 %10, 52
  %20 = and i64 %19, 2048
  %and13.i = or i64 %shl22.i, %12
  %or17.i = or i64 %and13.i, %18
  %and25.i = or i64 %or17.i, %20
  %or29.i = or i64 %and25.i, %shl16.i
  %or30.i = or i64 %or29.i, %16
  %sub.i64 = add i64 %6, -6
  store i64 %sub.i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i65 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i64
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i65 to i64*
  store i64 %or.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %21 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i66 = add i64 %21, -8
  store i64 %sub.i66, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i67 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i66
  %value.addr.0.arrayidx.sroa_cast.i68 = bitcast i8* %arrayidx.i67 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i68, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHLDIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i32*
  %value.0.copyload.i55 = load i32, i32* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i56 = trunc i64 %3 to i32
  store i32 %conv.i.i56, i32* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i57 = add i64 %4, 4
  store i64 %add.i57, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i58 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i57
  %value.0.arrayidx.sroa_cast.i59 = bitcast i8* %arrayidx.i58 to i16*
  %value.0.copyload.i60 = load i16, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i61 = trunc i64 %5 to i16
  store i16 %conv.i.i61, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i62 = add i64 %6, 2
  store i64 %add.i62, i64* %vsp, align 8, !tbaa !4
  %7 = and i16 %value.0.copyload.i60, 31
  %conv.i = zext i32 %value.0.copyload.i to i64
  %conv1.i = zext i16 %7 to i32
  %shl.i = shl i32 %value.0.copyload.i, %conv1.i
  %narrow = sub nuw nsw i16 32, %7
  %conv.i63 = zext i32 %value.0.copyload.i55 to i64
  %conv1.i64 = zext i16 %narrow to i64
  %shr.i = lshr i64 %conv.i63, %conv1.i64
  %conv2.i65 = trunc i64 %shr.i to i32
  %or3.i = or i32 %shl.i, %conv2.i65
  %conv.i.i66 = trunc i32 %or3.i to i8
  %8 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i66) #3, !range !10
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i67 = trunc i64 %9 to i8
  %tobool.not = icmp eq i8 %conv.i67, 0
  %cmp.i.i = icmp eq i32 %or3.i, 0
  %10 = xor i32 %or3.i, %value.0.copyload.i
  %11 = lshr i64 %conv.i, %conv1.i64
  %12 = and i64 %11, 1
  %13 = shl nuw nsw i8 %8, 2
  %14 = and i8 %13, 4
  %15 = xor i8 %14, 4
  %16 = zext i8 %15 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %17 = lshr i32 %or3.i, 24
  %18 = and i32 %17, 128
  %19 = zext i32 %18 to i64
  %20 = lshr i32 %10, 20
  %21 = and i32 %20, 2048
  %22 = zext i32 %21 to i64
  %and13.i = or i64 %shl22.i, %12
  %or17.i = or i64 %and13.i, %shl16.i
  %and25.i = or i64 %or17.i, %19
  %or29.i = or i64 %and25.i, %22
  %or30.i = or i64 %or29.i, %16
  %sub.i70 = add i64 %6, -2
  store i64 %sub.i70, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i71 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i70
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i71 to i32*
  store i32 %or3.i, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %23 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i72 = add i64 %23, -8
  store i64 %sub.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i72
  %value.addr.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i74, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHLDItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i16*
  %value.0.copyload.i55 = load i16, i16* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i56 = trunc i64 %3 to i16
  store i16 %conv.i.i56, i16* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i57 = add i64 %4, 2
  store i64 %add.i57, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i58 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i57
  %value.0.arrayidx.sroa_cast.i59 = bitcast i8* %arrayidx.i58 to i16*
  %value.0.copyload.i60 = load i16, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i61 = trunc i64 %5 to i16
  store i16 %conv.i.i61, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i62 = add i64 %6, 2
  store i64 %add.i62, i64* %vsp, align 8, !tbaa !4
  %and3.i = and i16 %value.0.copyload.i60, 31
  %conv.i = zext i16 %value.0.copyload.i to i64
  %conv1.i = zext i16 %and3.i to i64
  %shl.i = shl nuw nsw i64 %conv.i, %conv1.i
  %sub.i = sub nsw i16 16, %and3.i
  %conv.i63 = zext i16 %value.0.copyload.i55 to i64
  %conv1.i64 = zext i16 %sub.i to i64
  %shr.i = lshr i64 %conv.i63, %conv1.i64
  %or3.i77 = or i64 %shr.i, %shl.i
  %or3.i = trunc i64 %or3.i77 to i16
  %conv.i.i66 = trunc i64 %or3.i77 to i8
  %7 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i66) #3, !range !10
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i67 = trunc i64 %8 to i8
  %tobool.not = icmp eq i8 %conv.i67, 0
  %cmp.i.i = icmp eq i16 %or3.i, 0
  %9 = xor i16 %value.0.copyload.i, %or3.i
  %10 = lshr i64 %conv.i, %conv1.i64
  %11 = and i64 %10, 1
  %12 = shl nuw nsw i8 %7, 2
  %13 = and i8 %12, 4
  %14 = xor i8 %13, 4
  %15 = zext i8 %14 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %16 = lshr i64 %or3.i77, 8
  %17 = and i64 %16, 128
  %18 = lshr i16 %9, 4
  %19 = and i16 %18, 2048
  %20 = zext i16 %19 to i64
  %and13.i = or i64 %17, %11
  %or17.i = or i64 %and13.i, %shl22.i
  %and25.i = or i64 %or17.i, %shl16.i
  %or29.i = or i64 %and25.i, %20
  %or30.i = or i64 %or29.i, %15
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i71 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i71 to i16*
  store i16 %or3.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %21 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i72 = add i64 %21, -8
  store i64 %sub.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i72
  %value.addr.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i74, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHLDIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.copyload.i = load i8, i8* %arrayidx.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i8
  store i8 %conv.i.i, i8* %arrayidx.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 1
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i42 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.copyload.i43 = load i8, i8* %arrayidx.i42, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i44 = trunc i64 %3 to i8
  store i8 %conv.i.i44, i8* %arrayidx.i42, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i45 = add i64 %4, 1
  store i64 %add.i45, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i46 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i45
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i46 to i16*
  %value.0.copyload.i47 = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i48 = trunc i64 %5 to i16
  store i16 %conv.i.i48, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i49 = add i64 %6, 2
  store i64 %add.i49, i64* %vsp, align 8, !tbaa !4
  %conv = trunc i16 %value.0.copyload.i47 to i8
  %and3.i = and i8 %conv, 31
  %conv.i = zext i8 %value.0.copyload.i to i64
  %conv1.i = zext i8 %and3.i to i64
  %shl.i = shl nuw nsw i64 %conv.i, %conv1.i
  %sub.i = sub nsw i8 8, %and3.i
  %conv.i50 = zext i8 %value.0.copyload.i43 to i64
  %conv1.i51 = zext i8 %sub.i to i64
  %shr.i = lshr i64 %conv.i50, %conv1.i51
  %or3.i62 = or i64 %shr.i, %shl.i
  %or3.i = trunc i64 %or3.i62 to i8
  %7 = tail call i8 @llvm.ctpop.i8(i8 %or3.i) #3, !range !10
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i53 = trunc i64 %8 to i8
  %tobool.not = icmp eq i8 %conv.i53, 0
  %cmp.i.i = icmp eq i8 %or3.i, 0
  %9 = xor i8 %value.0.copyload.i, %or3.i
  %10 = lshr i64 %conv.i, %conv1.i51
  %11 = and i64 %10, 1
  %12 = shl nuw nsw i8 %7, 2
  %13 = and i8 %12, 4
  %14 = xor i8 %13, 4
  %15 = zext i8 %14 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %16 = and i64 %or3.i62, 128
  %17 = and i8 %9, -128
  %18 = zext i8 %17 to i64
  %19 = shl nuw nsw i64 %18, 4
  %and25.i = or i64 %16, %shl22.i
  %and13.i = or i64 %shl16.i, %11
  %or17.i = or i64 %and13.i, %and25.i
  %or29.i = or i64 %or17.i, %19
  %or30.i = or i64 %or29.i, %15
  %sub.i56 = add i64 %6, 1
  store i64 %sub.i56, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i56
  store i8 %or3.i, i8* %arrayidx.i57, align 1
  %20 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i58 = add i64 %20, -8
  store i64 %sub.i58, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i58
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i59 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHRDImEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i64*
  %value.0.copyload.i55 = load i64, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i56 = add i64 %4, 8
  store i64 %add.i56, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i56
  %value.0.arrayidx.sroa_cast.i58 = bitcast i8* %arrayidx.i57 to i16*
  %value.0.copyload.i59 = load i16, i16* %value.0.arrayidx.sroa_cast.i58, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %5 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i58, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i60 = add i64 %6, 2
  store i64 %add.i60, i64* %vsp, align 8, !tbaa !4
  %7 = and i16 %value.0.copyload.i59, 63
  %and.i = zext i16 %7 to i64
  %or.i = tail call i64 @llvm.fshr.i64(i64 %value.0.copyload.i55, i64 %value.0.copyload.i, i64 %and.i)
  %sub.i.i.i = add nsw i64 %and.i, -1
  %conv.i.i61 = trunc i64 %or.i to i8
  %8 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i61) #3, !range !10
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i = trunc i64 %9 to i8
  %tobool.not = icmp eq i8 %conv.i, 0
  %cmp.i.i = icmp eq i64 %or.i, 0
  %10 = xor i64 %or.i, %value.0.copyload.i
  %11 = lshr i64 %value.0.copyload.i, %sub.i.i.i
  %12 = and i64 %11, 1
  %13 = shl nuw nsw i8 %8, 2
  %14 = and i8 %13, 4
  %15 = xor i8 %14, 4
  %16 = zext i8 %15 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %17 = lshr i64 %or.i, 56
  %18 = and i64 %17, 128
  %19 = lshr i64 %10, 52
  %20 = and i64 %19, 2048
  %and13.i = or i64 %18, %shl22.i
  %or17.i = or i64 %and13.i, %12
  %and25.i = or i64 %or17.i, %20
  %or29.i = or i64 %and25.i, %shl16.i
  %or30.i = or i64 %or29.i, %16
  %sub.i64 = add i64 %6, -6
  store i64 %sub.i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i65 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i64
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i65 to i64*
  store i64 %or.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %21 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i66 = add i64 %21, -8
  store i64 %sub.i66, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i67 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i66
  %value.addr.0.arrayidx.sroa_cast.i68 = bitcast i8* %arrayidx.i67 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i68, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHRDIjEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i32*
  %value.0.copyload.i = load i32, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i32
  store i32 %conv.i.i, i32* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 4
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i32*
  %value.0.copyload.i55 = load i32, i32* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i56 = trunc i64 %3 to i32
  store i32 %conv.i.i56, i32* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i57 = add i64 %4, 4
  store i64 %add.i57, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i58 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i57
  %value.0.arrayidx.sroa_cast.i59 = bitcast i8* %arrayidx.i58 to i16*
  %value.0.copyload.i60 = load i16, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i61 = trunc i64 %5 to i16
  store i16 %conv.i.i61, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i62 = add i64 %6, 2
  store i64 %add.i62, i64* %vsp, align 8, !tbaa !4
  %7 = and i16 %value.0.copyload.i60, 31
  %and3.i = zext i16 %7 to i32
  %sub.i = sub nuw nsw i32 32, %and3.i
  %conv.i = zext i32 %value.0.copyload.i55 to i64
  %conv1.i = zext i32 %sub.i to i64
  %shl.i = shl nuw i64 %conv.i, %conv1.i
  %conv2.i = trunc i64 %shl.i to i32
  %conv.i63 = zext i32 %value.0.copyload.i to i64
  %shr.i = lshr i32 %value.0.copyload.i, %and3.i
  %or3.i = or i32 %shr.i, %conv2.i
  %sub.i.i.i = add nsw i32 %and3.i, -1
  %conv1.i.i.i = zext i32 %sub.i.i.i to i64
  %conv.i.i66 = trunc i32 %or3.i to i8
  %8 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i66) #3, !range !10
  %9 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i67 = trunc i64 %9 to i8
  %tobool.not = icmp eq i8 %conv.i67, 0
  %cmp.i.i = icmp eq i32 %or3.i, 0
  %10 = xor i32 %or3.i, %value.0.copyload.i
  %11 = lshr i64 %conv.i63, %conv1.i.i.i
  %12 = and i64 %11, 1
  %13 = shl nuw nsw i8 %8, 2
  %14 = and i8 %13, 4
  %15 = xor i8 %14, 4
  %16 = zext i8 %15 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %17 = lshr i32 %or3.i, 24
  %18 = and i32 %17, 128
  %19 = zext i32 %18 to i64
  %20 = lshr i32 %10, 20
  %21 = and i32 %20, 2048
  %22 = zext i32 %21 to i64
  %and13.i = or i64 %shl16.i, %12
  %or17.i = or i64 %and13.i, %shl22.i
  %and25.i = or i64 %or17.i, %19
  %or29.i = or i64 %and25.i, %22
  %or30.i = or i64 %or29.i, %16
  %sub.i70 = add i64 %6, -2
  store i64 %sub.i70, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i71 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i70
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i71 to i32*
  store i32 %or3.i, i32* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %23 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i72 = add i64 %23, -8
  store i64 %sub.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i72
  %value.addr.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i74, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHRDItEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i16*
  %value.0.copyload.i = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i16
  store i16 %conv.i.i, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 2
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i53 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.arrayidx.sroa_cast.i54 = bitcast i8* %arrayidx.i53 to i16*
  %value.0.copyload.i55 = load i16, i16* %value.0.arrayidx.sroa_cast.i54, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i56 = trunc i64 %3 to i16
  store i16 %conv.i.i56, i16* %value.0.arrayidx.sroa_cast.i54, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i57 = add i64 %4, 2
  store i64 %add.i57, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i58 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i57
  %value.0.arrayidx.sroa_cast.i59 = bitcast i8* %arrayidx.i58 to i16*
  %value.0.copyload.i60 = load i16, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i61 = trunc i64 %5 to i16
  store i16 %conv.i.i61, i16* %value.0.arrayidx.sroa_cast.i59, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i62 = add i64 %6, 2
  store i64 %add.i62, i64* %vsp, align 8, !tbaa !4
  %and3.i = and i16 %value.0.copyload.i60, 31
  %sub.i = sub nsw i16 16, %and3.i
  %conv.i = zext i16 %value.0.copyload.i55 to i64
  %conv1.i = zext i16 %sub.i to i64
  %shl.i = shl i64 %conv.i, %conv1.i
  %conv.i63 = zext i16 %value.0.copyload.i to i64
  %conv1.i64 = zext i16 %and3.i to i64
  %shr.i = lshr i64 %conv.i63, %conv1.i64
  %or3.i77 = or i64 %shl.i, %shr.i
  %or3.i = trunc i64 %or3.i77 to i16
  %sub.i.i.i = add nsw i16 %and3.i, -1
  %conv1.i.i.i = zext i16 %sub.i.i.i to i64
  %conv.i.i66 = trunc i64 %or3.i77 to i8
  %7 = tail call i8 @llvm.ctpop.i8(i8 %conv.i.i66) #3, !range !10
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i67 = trunc i64 %8 to i8
  %tobool.not = icmp eq i8 %conv.i67, 0
  %cmp.i.i = icmp eq i16 %or3.i, 0
  %9 = xor i16 %value.0.copyload.i, %or3.i
  %10 = lshr i64 %conv.i63, %conv1.i.i.i
  %11 = and i64 %10, 1
  %12 = shl nuw nsw i8 %7, 2
  %13 = and i8 %12, 4
  %14 = xor i8 %13, 4
  %15 = zext i8 %14 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %16 = lshr i64 %or3.i77, 8
  %17 = and i64 %16, 128
  %18 = lshr i16 %9, 4
  %19 = and i16 %18, 2048
  %20 = zext i16 %19 to i64
  %and13.i = or i64 %17, %11
  %or17.i = or i64 %and13.i, %shl22.i
  %and25.i = or i64 %or17.i, %shl16.i
  %or29.i = or i64 %and25.i, %20
  %or30.i = or i64 %or29.i, %15
  store i64 %6, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i71 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %6
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i71 to i16*
  store i16 %or3.i, i16* %value.addr.0.arrayidx.sroa_cast.i, align 1
  %21 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i72 = add i64 %21, -8
  store i64 %sub.i72, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i73 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i72
  %value.addr.0.arrayidx.sroa_cast.i74 = bitcast i8* %arrayidx.i73 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i74, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define linkonce_odr dso_local void @_Z4SHRDIhEvRm(i64* nonnull align 8 dereferenceable(8) %vsp) #0 comdat {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.copyload.i = load i8, i8* %arrayidx.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i = trunc i64 %1 to i8
  store i8 %conv.i.i, i8* %arrayidx.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 1
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i42 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i
  %value.0.copyload.i43 = load i8, i8* %arrayidx.i42, align 1
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i44 = trunc i64 %3 to i8
  store i8 %conv.i.i44, i8* %arrayidx.i42, align 1
  %4 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i45 = add i64 %4, 1
  store i64 %add.i45, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i46 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %add.i45
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i46 to i16*
  %value.0.copyload.i47 = load i16, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %5 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i.i48 = trunc i64 %5 to i16
  store i16 %conv.i.i48, i16* %value.0.arrayidx.sroa_cast.i, align 1
  %6 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i49 = add i64 %6, 2
  store i64 %add.i49, i64* %vsp, align 8, !tbaa !4
  %conv = trunc i16 %value.0.copyload.i47 to i8
  %and3.i = and i8 %conv, 31
  %sub.i = sub nsw i8 8, %and3.i
  %conv.i = zext i8 %value.0.copyload.i43 to i64
  %conv1.i = zext i8 %sub.i to i64
  %shl.i = shl i64 %conv.i, %conv1.i
  %conv.i50 = zext i8 %value.0.copyload.i to i64
  %conv1.i51 = zext i8 %and3.i to i64
  %shr.i = lshr i64 %conv.i50, %conv1.i51
  %or3.i62 = or i64 %shl.i, %shr.i
  %or3.i = trunc i64 %or3.i62 to i8
  %sub.i.i.i = add nsw i8 %and3.i, -1
  %conv1.i.i.i = zext i8 %sub.i.i.i to i64
  %7 = tail call i8 @llvm.ctpop.i8(i8 %or3.i) #3, !range !10
  %8 = load i64, i64* @__undef, align 8, !tbaa !4
  %conv.i53 = trunc i64 %8 to i8
  %tobool.not = icmp eq i8 %conv.i53, 0
  %cmp.i.i = icmp eq i8 %or3.i, 0
  %9 = xor i8 %value.0.copyload.i, %or3.i
  %10 = lshr i64 %conv.i50, %conv1.i.i.i
  %11 = and i64 %10, 1
  %12 = shl nuw nsw i8 %7, 2
  %13 = and i8 %12, 4
  %14 = xor i8 %13, 4
  %15 = zext i8 %14 to i64
  %shl16.i = select i1 %tobool.not, i64 0, i64 16
  %shl22.i = select i1 %cmp.i.i, i64 64, i64 0
  %16 = and i64 %or3.i62, 128
  %17 = and i8 %9, -128
  %18 = zext i8 %17 to i64
  %19 = shl nuw nsw i64 %18, 4
  %and25.i = or i64 %16, %shl22.i
  %and13.i = or i64 %shl16.i, %11
  %or17.i = or i64 %and13.i, %and25.i
  %or29.i = or i64 %or17.i, %19
  %or30.i = or i64 %or29.i, %15
  %sub.i56 = add i64 %6, 1
  store i64 %sub.i56, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i57 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i56
  store i8 %or3.i, i8* %arrayidx.i57, align 1
  %20 = load i64, i64* %vsp, align 8, !tbaa !4
  %sub.i58 = add i64 %20, -8
  store i64 %sub.i58, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i59 = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %sub.i58
  %value.addr.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i59 to i64*
  store i64 %or30.i, i64* %value.addr.0.arrayidx.sroa_cast.i, align 1
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z4JUMPRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %vip) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  store i64 %value.0.copyload.i, i64* %vip, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z8JUMP_DECRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %vip) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %sub = add i64 %value.0.copyload.i, -4
  store i64 %sub, i64* %vip, align 8, !tbaa !4
  ret void
}

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn
define dso_local void @_Z8JUMP_INCRmS_(i64* nocapture nonnull align 8 dereferenceable(8) %vsp, i64* nocapture nonnull align 8 dereferenceable(8) %vip) #2 {
entry:
  %0 = load i64, i64* %vsp, align 8, !tbaa !4
  %arrayidx.i = getelementptr inbounds [0 x i8], [0 x i8]* @RAM, i64 0, i64 %0
  %value.0.arrayidx.sroa_cast.i = bitcast i8* %arrayidx.i to i64*
  %value.0.copyload.i = load i64, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %1 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %1, i64* %value.0.arrayidx.sroa_cast.i, align 1
  %2 = load i64, i64* %vsp, align 8, !tbaa !4
  %add.i = add i64 %2, 8
  store i64 %add.i, i64* %vsp, align 8, !tbaa !4
  %add = add i64 %value.0.copyload.i, 4
  store i64 %add, i64* %vip, align 8, !tbaa !4
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define dso_local void @HelperUnsupported(i64* noalias nocapture nonnull align 8 dereferenceable(8) %rax, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rbx, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rcx, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rdx, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rsi, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rdi, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rbp, i64* noalias nocapture nonnull align 8 dereferenceable(8) %rsp, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r8, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r9, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r10, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r11, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r12, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r13, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r14, i64* noalias nocapture nonnull align 8 dereferenceable(8) %r15) local_unnamed_addr #4 {
entry:
  %ctx = alloca %struct.VirtualContext, align 8
  %0 = bitcast %struct.VirtualContext* %ctx to i8*
  call void @llvm.lifetime.start.p0i8(i64 128, i8* nonnull %0) #3
  %1 = load i64, i64* %rax, align 8, !tbaa !4
  %qword = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 0, i32 0, i32 0
  store i64 %1, i64* %qword, align 8, !tbaa !8
  %2 = load i64, i64* %rbx, align 8, !tbaa !4
  %qword3 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 1, i32 0, i32 0
  store i64 %2, i64* %qword3, align 8, !tbaa !8
  %3 = load i64, i64* %rcx, align 8, !tbaa !4
  %qword5 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 2, i32 0, i32 0
  store i64 %3, i64* %qword5, align 8, !tbaa !8
  %4 = load i64, i64* %rdx, align 8, !tbaa !4
  %qword7 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 3, i32 0, i32 0
  store i64 %4, i64* %qword7, align 8, !tbaa !8
  %5 = load i64, i64* %rsi, align 8, !tbaa !4
  %qword9 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 4, i32 0, i32 0
  store i64 %5, i64* %qword9, align 8, !tbaa !8
  %6 = load i64, i64* %rdi, align 8, !tbaa !4
  %qword11 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 5, i32 0, i32 0
  store i64 %6, i64* %qword11, align 8, !tbaa !8
  %7 = load i64, i64* %rbp, align 8, !tbaa !4
  %qword13 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 6, i32 0, i32 0
  store i64 %7, i64* %qword13, align 8, !tbaa !8
  %8 = load i64, i64* %rsp, align 8, !tbaa !4
  %qword15 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 7, i32 0, i32 0
  store i64 %8, i64* %qword15, align 8, !tbaa !8
  %9 = load i64, i64* %r8, align 8, !tbaa !4
  %qword17 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 8, i32 0, i32 0
  store i64 %9, i64* %qword17, align 8, !tbaa !8
  %10 = load i64, i64* %r9, align 8, !tbaa !4
  %qword19 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 9, i32 0, i32 0
  store i64 %10, i64* %qword19, align 8, !tbaa !8
  %11 = load i64, i64* %r10, align 8, !tbaa !4
  %qword21 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 10, i32 0, i32 0
  store i64 %11, i64* %qword21, align 8, !tbaa !8
  %12 = load i64, i64* %r11, align 8, !tbaa !4
  %qword23 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 11, i32 0, i32 0
  store i64 %12, i64* %qword23, align 8, !tbaa !8
  %13 = load i64, i64* %r12, align 8, !tbaa !4
  %qword25 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 12, i32 0, i32 0
  store i64 %13, i64* %qword25, align 8, !tbaa !8
  %14 = load i64, i64* %r13, align 8, !tbaa !4
  %qword27 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 13, i32 0, i32 0
  store i64 %14, i64* %qword27, align 8, !tbaa !8
  %15 = load i64, i64* %r14, align 8, !tbaa !4
  %qword29 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 14, i32 0, i32 0
  store i64 %15, i64* %qword29, align 8, !tbaa !8
  %16 = load i64, i64* %r15, align 8, !tbaa !4
  %qword31 = getelementptr inbounds %struct.VirtualContext, %struct.VirtualContext* %ctx, i64 0, i32 15, i32 0, i32 0
  store i64 %16, i64* %qword31, align 8, !tbaa !8
  call void @HelperUnsupportedStub(%struct.VirtualContext* nonnull align 1 dereferenceable(128) %ctx) #3
  %17 = load i64, i64* %qword, align 8, !tbaa !8
  store i64 %17, i64* %rax, align 8, !tbaa !4
  %18 = load i64, i64* %qword3, align 8, !tbaa !8
  store i64 %18, i64* %rbx, align 8, !tbaa !4
  %19 = load i64, i64* %qword5, align 8, !tbaa !8
  store i64 %19, i64* %rcx, align 8, !tbaa !4
  %20 = load i64, i64* %qword7, align 8, !tbaa !8
  store i64 %20, i64* %rdx, align 8, !tbaa !4
  %21 = load i64, i64* %qword9, align 8, !tbaa !8
  store i64 %21, i64* %rsi, align 8, !tbaa !4
  %22 = load i64, i64* %qword11, align 8, !tbaa !8
  store i64 %22, i64* %rdi, align 8, !tbaa !4
  %23 = load i64, i64* %qword13, align 8, !tbaa !8
  store i64 %23, i64* %rbp, align 8, !tbaa !4
  %24 = load i64, i64* %qword15, align 8, !tbaa !8
  store i64 %24, i64* %rsp, align 8, !tbaa !4
  %25 = load i64, i64* %qword17, align 8, !tbaa !8
  store i64 %25, i64* %r8, align 8, !tbaa !4
  %26 = load i64, i64* %qword19, align 8, !tbaa !8
  store i64 %26, i64* %r9, align 8, !tbaa !4
  %27 = load i64, i64* %qword21, align 8, !tbaa !8
  store i64 %27, i64* %r10, align 8, !tbaa !4
  %28 = load i64, i64* %qword23, align 8, !tbaa !8
  store i64 %28, i64* %r11, align 8, !tbaa !4
  %29 = load i64, i64* %qword25, align 8, !tbaa !8
  store i64 %29, i64* %r12, align 8, !tbaa !4
  %30 = load i64, i64* %qword27, align 8, !tbaa !8
  store i64 %30, i64* %r13, align 8, !tbaa !4
  %31 = load i64, i64* %qword29, align 8, !tbaa !8
  store i64 %31, i64* %r14, align 8, !tbaa !4
  %32 = load i64, i64* %qword31, align 8, !tbaa !8
  store i64 %32, i64* %r15, align 8, !tbaa !4
  call void @llvm.lifetime.end.p0i8(i64 128, i8* nonnull %0) #3
  ret void
}

declare dso_local void @HelperUnsupportedStub(%struct.VirtualContext* nonnull align 1 dereferenceable(128)) local_unnamed_addr #5

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind readonly uwtable willreturn
define dso_local i64 @HelperStubEmpty(i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rax, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rbx, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rcx, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rdx, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rsi, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rdi, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rbp, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %rsp, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r8, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r9, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r10, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r11, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r12, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r13, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r14, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %r15, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %flags, i64 %KEY_STUB, i64 %RET_ADDR, i64 %REL_ADDR, i64* noalias nocapture nonnull readnone align 8 dereferenceable(8) %vsp, i64* noalias nocapture nonnull readonly align 8 dereferenceable(8) %vip, %struct.VirtualRegister* noalias nocapture readnone %vmregs, i64* noalias nocapture readnone %slots) local_unnamed_addr #6 {
entry:
  %0 = load i64, i64* %vip, align 8, !tbaa !4
  ret i64 %0
}

; Function Attrs: alwaysinline mustprogress nounwind uwtable
define dso_local i64 @HelperFunction(i64* noalias nonnull align 8 dereferenceable(8) %rax, i64* noalias nonnull align 8 dereferenceable(8) %rbx, i64* noalias nonnull align 8 dereferenceable(8) %rcx, i64* noalias nonnull align 8 dereferenceable(8) %rdx, i64* noalias nonnull align 8 dereferenceable(8) %rsi, i64* noalias nonnull align 8 dereferenceable(8) %rdi, i64* noalias nonnull align 8 dereferenceable(8) %rbp, i64* noalias nonnull align 8 dereferenceable(8) %rsp, i64* noalias nonnull align 8 dereferenceable(8) %r8, i64* noalias nonnull align 8 dereferenceable(8) %r9, i64* noalias nonnull align 8 dereferenceable(8) %r10, i64* noalias nonnull align 8 dereferenceable(8) %r11, i64* noalias nonnull align 8 dereferenceable(8) %r12, i64* noalias nonnull align 8 dereferenceable(8) %r13, i64* noalias nonnull align 8 dereferenceable(8) %r14, i64* noalias nonnull align 8 dereferenceable(8) %r15, i64* noalias nonnull align 8 dereferenceable(8) %flags, i64 %KEY_STUB, i64 %RET_ADDR, i64 %REL_ADDR) local_unnamed_addr #0 {
entry:
  %vmregs = alloca [30 x %struct.VirtualRegister], align 16
  %slots = alloca [30 x i64], align 16
  %vip = alloca i64, align 8
  %0 = bitcast [30 x %struct.VirtualRegister]* %vmregs to i8*
  call void @llvm.lifetime.start.p0i8(i64 240, i8* nonnull %0) #3
  call void @llvm.memset.p0i8.i64(i8* noundef nonnull align 16 dereferenceable(240) %0, i8 0, i64 240, i1 false)
  %1 = bitcast [30 x i64]* %slots to i8*
  call void @llvm.lifetime.start.p0i8(i64 240, i8* nonnull %1) #3
  call void @llvm.memset.p0i8.i64(i8* noundef nonnull align 16 dereferenceable(240) %1, i8 0, i64 240, i1 false)
  %2 = bitcast i64* %vip to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %2) #3
  store i64 0, i64* %vip, align 8, !tbaa !4
  %arraydecay = getelementptr inbounds [30 x %struct.VirtualRegister], [30 x %struct.VirtualRegister]* %vmregs, i64 0, i64 0
  %arraydecay1 = getelementptr inbounds [30 x i64], [30 x i64]* %slots, i64 0, i64 0
  %call = call i64 @HelperStub(i64* nonnull align 8 dereferenceable(8) %rax, i64* nonnull align 8 dereferenceable(8) %rbx, i64* nonnull align 8 dereferenceable(8) %rcx, i64* nonnull align 8 dereferenceable(8) %rdx, i64* nonnull align 8 dereferenceable(8) %rsi, i64* nonnull align 8 dereferenceable(8) %rdi, i64* nonnull align 8 dereferenceable(8) %rbp, i64* nonnull align 8 dereferenceable(8) %rsp, i64* nonnull align 8 dereferenceable(8) %r8, i64* nonnull align 8 dereferenceable(8) %r9, i64* nonnull align 8 dereferenceable(8) %r10, i64* nonnull align 8 dereferenceable(8) %r11, i64* nonnull align 8 dereferenceable(8) %r12, i64* nonnull align 8 dereferenceable(8) %r13, i64* nonnull align 8 dereferenceable(8) %r14, i64* nonnull align 8 dereferenceable(8) %r15, i64* nonnull align 8 dereferenceable(8) %flags, i64 %KEY_STUB, i64 %RET_ADDR, i64 0, i64* nonnull align 8 dereferenceable(8) %rsp, i64* nonnull align 8 dereferenceable(8) %vip, %struct.VirtualRegister* nonnull %arraydecay, i64* nonnull %arraydecay1) #3
  %3 = load i64, i64* @__undef, align 8, !tbaa !4
  store i64 %3, i64* %flags, align 8, !tbaa !4
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %2) #3
  call void @llvm.lifetime.end.p0i8(i64 240, i8* nonnull %1) #3
  call void @llvm.lifetime.end.p0i8(i64 240, i8* nonnull %0) #3
  ret i64 %call
}

; Function Attrs: argmemonly mustprogress nofree nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #7

declare dso_local i64 @HelperStub(i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), i64, i64, i64, i64* nonnull align 8 dereferenceable(8), i64* nonnull align 8 dereferenceable(8), %struct.VirtualRegister*, i64*) local_unnamed_addr #5

; Function Attrs: mustprogress nounwind uwtable
define dso_local i64 @HelperSlicePC(i64 %rax, i64 %rbx, i64 %rcx, i64 %rdx, i64 %rsi, i64 %rdi, i64 %rbp, i64 %rsp, i64 %r8, i64 %r9, i64 %r10, i64 %r11, i64 %r12, i64 %r13, i64 %r14, i64 %r15, i64 %flags, i64 %KEY_STUB, i64 %RET_ADDR, i64 %REL_ADDR) local_unnamed_addr #4 {
entry:
  %rax.addr = alloca i64, align 8
  %rbx.addr = alloca i64, align 8
  %rcx.addr = alloca i64, align 8
  %rdx.addr = alloca i64, align 8
  %rsi.addr = alloca i64, align 8
  %rdi.addr = alloca i64, align 8
  %rbp.addr = alloca i64, align 8
  %rsp.addr = alloca i64, align 8
  %r8.addr = alloca i64, align 8
  %r9.addr = alloca i64, align 8
  %r10.addr = alloca i64, align 8
  %r11.addr = alloca i64, align 8
  %r12.addr = alloca i64, align 8
  %r13.addr = alloca i64, align 8
  %r14.addr = alloca i64, align 8
  %r15.addr = alloca i64, align 8
  %flags.addr = alloca i64, align 8
  %vmregs = alloca [30 x %struct.VirtualRegister], align 16
  %slots = alloca [30 x i64], align 16
  %vsp = alloca i64, align 8
  %vip = alloca i64, align 8
  store i64 %rax, i64* %rax.addr, align 8, !tbaa !4
  store i64 %rbx, i64* %rbx.addr, align 8, !tbaa !4
  store i64 %rcx, i64* %rcx.addr, align 8, !tbaa !4
  store i64 %rdx, i64* %rdx.addr, align 8, !tbaa !4
  store i64 %rsi, i64* %rsi.addr, align 8, !tbaa !4
  store i64 %rdi, i64* %rdi.addr, align 8, !tbaa !4
  store i64 %rbp, i64* %rbp.addr, align 8, !tbaa !4
  store i64 %rsp, i64* %rsp.addr, align 8, !tbaa !4
  store i64 %r8, i64* %r8.addr, align 8, !tbaa !4
  store i64 %r9, i64* %r9.addr, align 8, !tbaa !4
  store i64 %r10, i64* %r10.addr, align 8, !tbaa !4
  store i64 %r11, i64* %r11.addr, align 8, !tbaa !4
  store i64 %r12, i64* %r12.addr, align 8, !tbaa !4
  store i64 %r13, i64* %r13.addr, align 8, !tbaa !4
  store i64 %r14, i64* %r14.addr, align 8, !tbaa !4
  store i64 %r15, i64* %r15.addr, align 8, !tbaa !4
  store i64 %flags, i64* %flags.addr, align 8, !tbaa !4
  %0 = bitcast [30 x %struct.VirtualRegister]* %vmregs to i8*
  call void @llvm.lifetime.start.p0i8(i64 240, i8* nonnull %0) #3
  call void @llvm.memset.p0i8.i64(i8* noundef nonnull align 16 dereferenceable(240) %0, i8 0, i64 240, i1 false)
  %1 = bitcast [30 x i64]* %slots to i8*
  call void @llvm.lifetime.start.p0i8(i64 240, i8* nonnull %1) #3
  call void @llvm.memset.p0i8.i64(i8* noundef nonnull align 16 dereferenceable(240) %1, i8 0, i64 240, i1 false)
  %2 = bitcast i64* %vsp to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %2) #3
  store i64 %rsp, i64* %vsp, align 8, !tbaa !4
  %3 = bitcast i64* %vip to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %3) #3
  store i64 0, i64* %vip, align 8, !tbaa !4
  %arraydecay = getelementptr inbounds [30 x %struct.VirtualRegister], [30 x %struct.VirtualRegister]* %vmregs, i64 0, i64 0
  %arraydecay1 = getelementptr inbounds [30 x i64], [30 x i64]* %slots, i64 0, i64 0
  %call = call i64 @HelperStub(i64* nonnull align 8 dereferenceable(8) %rax.addr, i64* nonnull align 8 dereferenceable(8) %rbx.addr, i64* nonnull align 8 dereferenceable(8) %rcx.addr, i64* nonnull align 8 dereferenceable(8) %rdx.addr, i64* nonnull align 8 dereferenceable(8) %rsi.addr, i64* nonnull align 8 dereferenceable(8) %rdi.addr, i64* nonnull align 8 dereferenceable(8) %rbp.addr, i64* nonnull align 8 dereferenceable(8) %rsp.addr, i64* nonnull align 8 dereferenceable(8) %r8.addr, i64* nonnull align 8 dereferenceable(8) %r9.addr, i64* nonnull align 8 dereferenceable(8) %r10.addr, i64* nonnull align 8 dereferenceable(8) %r11.addr, i64* nonnull align 8 dereferenceable(8) %r12.addr, i64* nonnull align 8 dereferenceable(8) %r13.addr, i64* nonnull align 8 dereferenceable(8) %r14.addr, i64* nonnull align 8 dereferenceable(8) %r15.addr, i64* nonnull align 8 dereferenceable(8) %flags.addr, i64 %KEY_STUB, i64 %RET_ADDR, i64 0, i64* nonnull align 8 dereferenceable(8) %vsp, i64* nonnull align 8 dereferenceable(8) %vip, %struct.VirtualRegister* nonnull %arraydecay, i64* nonnull %arraydecay1) #3
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %3) #3
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %2) #3
  call void @llvm.lifetime.end.p0i8(i64 240, i8* nonnull %1) #3
  call void @llvm.lifetime.end.p0i8(i64 240, i8* nonnull %0) #3
  ret i64 %call
}

; Function Attrs: mustprogress nofree nosync nounwind uwtable willreturn writeonly
define dso_local void @retainPointers() local_unnamed_addr #8 {
entry:
  %call = tail call i64 @HelperKeepPC(i64 0, i64 1) #12
  %conv = trunc i64 %call to i8
  store i8 %conv, i8* getelementptr inbounds ([0 x i8], [0 x i8]* @RAM, i64 0, i64 0), align 1, !tbaa !8
  store i8 0, i8* getelementptr inbounds ([0 x i8], [0 x i8]* @GS, i64 0, i64 0), align 1, !tbaa !8
  store i8 0, i8* getelementptr inbounds ([0 x i8], [0 x i8]* @FS, i64 0, i64 0), align 1, !tbaa !8
  ret void
}

; Function Attrs: mustprogress noduplicate nofree nosync nounwind readnone willreturn
declare dso_local i64 @HelperKeepPC(i64, i64) local_unnamed_addr #9

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare i8 @llvm.ctpop.i8(i8) #10

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare i64 @llvm.fshr.i64(i64, i64, i64) #10

attributes #0 = { alwaysinline mustprogress nounwind uwtable "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #1 = { argmemonly mustprogress nofree nosync nounwind willreturn }
attributes #2 = { alwaysinline mustprogress nofree norecurse nosync nounwind uwtable willreturn "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #3 = { nounwind }
attributes #4 = { mustprogress nounwind uwtable "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #5 = { "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #6 = { alwaysinline mustprogress nofree norecurse nosync nounwind readonly uwtable willreturn "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #7 = { argmemonly mustprogress nofree nounwind willreturn writeonly }
attributes #8 = { mustprogress nofree nosync nounwind uwtable willreturn writeonly "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #9 = { mustprogress noduplicate nofree nosync nounwind readnone willreturn "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+x87,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-xop" "tune-cpu"="generic" }
attributes #10 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #11 = { nounwind readnone }
attributes #12 = { noduplicate nomerge nounwind readnone willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"uwtable", i32 1}
!2 = !{!"clang version 13.0.1"}
!3 = !{i64 3772}
!4 = !{!5, !5, i64 0}
!5 = !{!"long", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C++ TBAA"}
!8 = !{!6, !6, i64 0}
!9 = !{i64 2152664675, i64 2152664711, i64 2152664735}
!10 = !{i8 0, i8 9}
