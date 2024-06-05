use vstd::prelude::*;

verus! {

fn main() {}

fn imm_shift_from_imm64(/*&mut self, */ty: Type, val: Imm64) -> Option<ImmShift> {
    let imm_value = (val.bits() as u64) & ((ty.bits() - 1) as u64);
    ImmShift::maybe_from_u64(imm_value)
}

/// ---------------------------------------------------------------------------

/// Start of the lane types.
pub const LANE_BASE: u16 = 0x70;

/// Base for reference types.
pub const REFERENCE_BASE: u16 = 0x7E;

/// Start of the 2-lane vector types.
pub const VECTOR_BASE: u16 = 0x80;

/// Start of the dynamic vector types.
pub const DYNAMIC_VECTOR_BASE: u16 = 0x100;

/// ---------------------------------------------------------------------------

/// 64-bit immediate signed integer operand.
///
/// An `Imm64` operand can also be used to represent immediate values of smaller integer types by
/// sign-extending to `i64`.
pub struct Imm64(i64);

impl Imm64 {
    /// Create a new `Imm64` representing the signed number `x`.
    pub fn new(x: i64) -> Self {
        Self(x)
    }

    // /// Return self negated.
    // pub fn wrapping_neg(self) -> Self {
    //     Self(self.0.wrapping_neg())
    // }

    /// Returns the value of this immediate.
    pub fn bits(&self) -> i64 {
        self.0
    }

    ///// Sign extend this immediate as if it were a signed integer of the given
    ///// power-of-two width.
    //pub fn sign_extend_from_width(&mut self, bit_width: u32) {
    //    /*debug_assert!(bit_width.is_power_of_two());*/

    //    if bit_width >= 64 {
    //        return;
    //    }

    //    let bit_width = i64::from(bit_width);
    //    let delta = 64 - bit_width;
    //    let sign_extended = (self.0 << delta) >> delta;
    //    *self = Imm64(sign_extended);
    //}
}

/// An immediate for shift instructions.
pub struct ImmShift {
    /// 6-bit shift amount.
    pub imm: u8,
}

impl ImmShift {
    /// Create an ImmShift from raw bits, if possible.
    pub fn maybe_from_u64(val: u64) -> Option<ImmShift> {
        if val < 64 {
            Some(ImmShift { imm: val as u8 })
        } else {
            None
        }
    }

    /// Get the immediate value.
    pub fn value(&self) -> u8 {
        self.imm
    }
}

/// The type of an SSA value.
///
/// The `INVALID` type isn't a real type, and is used as a placeholder in the IR where a type
/// field is present put no type is needed, such as the controlling type variable for a
/// non-polymorphic instruction.
///
/// Basic integer types: `I8`, `I16`, `I32`, `I64`, and `I128`. These types are sign-agnostic.
///
/// Basic floating point types: `F32` and `F64`. IEEE single and double precision.
///
/// SIMD vector types have power-of-two lanes, up to 256. Lanes can be any int/float type.
///
/// Note that this is encoded in a `u16` currently for extensibility,
/// but allows only 14 bits to be used due to some bitpacking tricks
/// in the CLIF data structures.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Type(u16);

/*
/// Not a valid type. Can't be loaded or stored. Can't be part of a SIMD vector.
pub const INVALID: Type = Type(0);

/// ---------------------------------------------------------------------------

/// An integer type with 8 bits.
/// WARNING: arithmetic on 8bit integers is incomplete
pub const I8: Type = Type(0x76);

/// An integer type with 16 bits.
/// WARNING: arithmetic on 16bit integers is incomplete
pub const I16: Type = Type(0x77);

/// An integer type with 32 bits.
pub const I32: Type = Type(0x78);

/// An integer type with 64 bits.
pub const I64: Type = Type(0x79);

/// An integer type with 128 bits.
pub const I128: Type = Type(0x7a);

/// A 32-bit floating point type represented in the IEEE 754-2008
/// *binary32* interchange format. This corresponds to the :c:type:`float`
/// type in most C implementations.
pub const F32: Type = Type(0x7b);

/// A 64-bit floating point type represented in the IEEE 754-2008
/// *binary64* interchange format. This corresponds to the :c:type:`double`
/// type in most C implementations.
pub const F64: Type = Type(0x7c);

/// An opaque reference type with 32 bits.
pub const R32: Type = Type(0x7e);

/// An opaque reference type with 64 bits.
pub const R64: Type = Type(0x7f);

/// A SIMD vector with 2 lanes containing a `i8` each.
pub const I8X2: Type = Type(0x86);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `i8` bits each.
pub const I8X2XN: Type = Type(0x106);

/// A SIMD vector with 4 lanes containing a `i8` each.
pub const I8X4: Type = Type(0x96);

/// A SIMD vector with 2 lanes containing a `i16` each.
pub const I16X2: Type = Type(0x87);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `i8` bits each.
pub const I8X4XN: Type = Type(0x116);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `i16` bits each.
pub const I16X2XN: Type = Type(0x107);

/// A SIMD vector with 8 lanes containing a `i8` each.
pub const I8X8: Type = Type(0xa6);

/// A SIMD vector with 4 lanes containing a `i16` each.
pub const I16X4: Type = Type(0x97);

/// A SIMD vector with 2 lanes containing a `i32` each.
pub const I32X2: Type = Type(0x88);

/// A SIMD vector with 2 lanes containing a `f32` each.
pub const F32X2: Type = Type(0x8b);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `i8` bits each.
pub const I8X8XN: Type = Type(0x126);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `i16` bits each.
pub const I16X4XN: Type = Type(0x117);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `i32` bits each.
pub const I32X2XN: Type = Type(0x108);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `f32` bits each.
pub const F32X2XN: Type = Type(0x10b);

/// A SIMD vector with 16 lanes containing a `i8` each.
pub const I8X16: Type = Type(0xb6);

/// A SIMD vector with 8 lanes containing a `i16` each.
pub const I16X8: Type = Type(0xa7);

/// A SIMD vector with 4 lanes containing a `i32` each.
pub const I32X4: Type = Type(0x98);

/// A SIMD vector with 2 lanes containing a `i64` each.
pub const I64X2: Type = Type(0x89);

/// A SIMD vector with 4 lanes containing a `f32` each.
pub const F32X4: Type = Type(0x9b);

/// A SIMD vector with 2 lanes containing a `f64` each.
pub const F64X2: Type = Type(0x8c);

/// A dynamically-scaled SIMD vector with a minimum of 16 lanes containing `i8` bits each.
pub const I8X16XN: Type = Type(0x136);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `i16` bits each.
pub const I16X8XN: Type = Type(0x127);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `i32` bits each.
pub const I32X4XN: Type = Type(0x118);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `i64` bits each.
pub const I64X2XN: Type = Type(0x109);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `f32` bits each.
pub const F32X4XN: Type = Type(0x11b);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `f64` bits each.
pub const F64X2XN: Type = Type(0x10c);

/// A SIMD vector with 32 lanes containing a `i8` each.
pub const I8X32: Type = Type(0xc6);

/// A SIMD vector with 16 lanes containing a `i16` each.
pub const I16X16: Type = Type(0xb7);

/// A SIMD vector with 8 lanes containing a `i32` each.
pub const I32X8: Type = Type(0xa8);

/// A SIMD vector with 4 lanes containing a `i64` each.
pub const I64X4: Type = Type(0x99);

/// A SIMD vector with 2 lanes containing a `i128` each.
pub const I128X2: Type = Type(0x8a);

/// A SIMD vector with 8 lanes containing a `f32` each.
pub const F32X8: Type = Type(0xab);

/// A SIMD vector with 4 lanes containing a `f64` each.
pub const F64X4: Type = Type(0x9c);

/// A dynamically-scaled SIMD vector with a minimum of 32 lanes containing `i8` bits each.
pub const I8X32XN: Type = Type(0x146);

/// A dynamically-scaled SIMD vector with a minimum of 16 lanes containing `i16` bits each.
pub const I16X16XN: Type = Type(0x137);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `i32` bits each.
pub const I32X8XN: Type = Type(0x128);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `i64` bits each.
pub const I64X4XN: Type = Type(0x119);

/// A dynamically-scaled SIMD vector with a minimum of 2 lanes containing `i128` bits each.
pub const I128X2XN: Type = Type(0x10a);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `f32` bits each.
pub const F32X8XN: Type = Type(0x12b);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `f64` bits each.
pub const F64X4XN: Type = Type(0x11c);

/// A SIMD vector with 64 lanes containing a `i8` each.
pub const I8X64: Type = Type(0xd6);

/// A SIMD vector with 32 lanes containing a `i16` each.
pub const I16X32: Type = Type(0xc7);

/// A SIMD vector with 16 lanes containing a `i32` each.
pub const I32X16: Type = Type(0xb8);

/// A SIMD vector with 8 lanes containing a `i64` each.
pub const I64X8: Type = Type(0xa9);

/// A SIMD vector with 4 lanes containing a `i128` each.
pub const I128X4: Type = Type(0x9a);

/// A SIMD vector with 16 lanes containing a `f32` each.
pub const F32X16: Type = Type(0xbb);

/// A SIMD vector with 8 lanes containing a `f64` each.
pub const F64X8: Type = Type(0xac);

/// A dynamically-scaled SIMD vector with a minimum of 64 lanes containing `i8` bits each.
pub const I8X64XN: Type = Type(0x156);

/// A dynamically-scaled SIMD vector with a minimum of 32 lanes containing `i16` bits each.
pub const I16X32XN: Type = Type(0x147);

/// A dynamically-scaled SIMD vector with a minimum of 16 lanes containing `i32` bits each.
pub const I32X16XN: Type = Type(0x138);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `i64` bits each.
pub const I64X8XN: Type = Type(0x129);

/// A dynamically-scaled SIMD vector with a minimum of 4 lanes containing `i128` bits each.
pub const I128X4XN: Type = Type(0x11a);

/// A dynamically-scaled SIMD vector with a minimum of 16 lanes containing `f32` bits each.
pub const F32X16XN: Type = Type(0x13b);

/// A dynamically-scaled SIMD vector with a minimum of 8 lanes containing `f64` bits each.
pub const F64X8XN: Type = Type(0x12c);
*/
/// ---------------------------------------------------------------------------

impl Type {
    /// Get the total number of bits used to represent this type.
    pub fn bits(self) -> u32 {
        if self.is_dynamic_vector() {
            0
        } else {
            self.lane_bits() * self.lane_count()
        }
    }

    /// Is this a SIMD vector type with a runtime number of lanes?
    pub fn is_dynamic_vector(self) -> bool {
        self.0 >= /*constants::*/DYNAMIC_VECTOR_BASE
    }

    /// Get the lane type of this SIMD vector type.
    ///
    /// A lane type is the same as a SIMD vector type with one lane, so it returns itself.
    pub fn lane_type(self) -> Self {
        if self.0 < /*constants::*/VECTOR_BASE {
            self
        } else {
            Self(/*constants::*/LANE_BASE | (self.0 & 0x0f))
        }
    }

    /// Get the number of bits in a lane.
    pub fn lane_bits(self) -> u32 {
        match self.lane_type() {
            Type(x) if x == 0x76 => 8,
            /*I16 => 16,
            I32 | F32 | R32 => 32,
            I64 | F64 | R64 => 64,
            I128 => 128,*/
            _ => 0,
        }
    }

    /// Get the number of lanes in this SIMD vector type.
    ///
    /// A scalar type is the same as a SIMD vector type with one lane, so it returns 1.
    pub fn lane_count(self) -> u32 {
        if self.is_dynamic_vector() {
            0
        } else {
            1 << self.log2_lane_count()
        }
    }

    /// Get log_2 of the number of lanes in this SIMD vector type.
    ///
    /// All SIMD types have a lane count that is a power of two and no larger than 256, so this
    /// will be a number in the range 0-8.
    ///
    /// A scalar type is the same as a SIMD vector type with one lane, so it returns 0.
    pub fn log2_lane_count(self) -> u32 {
        if self.is_dynamic_vector() {
            0
        } else {
            (self.0.saturating_sub(/*constants::*/LANE_BASE) >> 4) as u32
        }
    }
}

}
