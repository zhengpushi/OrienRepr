# INTRODUCTION
`OrienRepr` is a formal verification project in Coq, for `Orientation Representation (OR)` problem, which is focused on derivation of popular models or algorithms for OR, including Euler Angles, Rotation Matrices, Axis-Angles, and Unit Quaternion.

Note that, project `OrienRepr` is part of project `VFCS` (Verified Flight Control System), but it is not published for now.

The entrance of the project is OrienRepr/OrienRepr.v.
For more details of different ORs, please check:
* RotationMatrix3D.v
* EulerAngle.v
* AxisAngle.v
* Quaternion.v

## Resources
* Homepage: [OrienRepr project](https://zhengpushi.github.io/projects/OrienRepr).
* Source-code: [OrienRepr github](https://github.com/zhengpushi/OrienRepr)


## Preparation
This project need FinMatrix library, which is a formal matrix library in Coq, and also developed by us.
* There are two ways to install FinMatrix
  * For stable version, use opam.
	`opam install coq-finmatrix`
  * For newest version, use source code.
	download the source code from [FinMatrix github](https://github.com/zhengpushi/FinMatrix), then
	`make; make install`

## Compile
```
make
make clean
make html
```
