# Introduction
`OrienRepr` is a formal verification project in Coq, for `Orientation Representation (OR)` problem, which is focused on derivation of popular models or algorithms for OR, including Euler Angles, Rotation Matrices, Axis-Angles, and Unit Quaternion.

Note that, project `OrienRepr` is part of project `VFCS` (Verified Flight Control System), but it is not published for now.


# Installation 
This project need FinMatrix library, which is a formal matrix library in Coq.
* There are two wasy to install FinMatrix
  * For stable version, use opam.
	`opam install coq-finmatrix`
  * For newest version, use source code.
	download the source code from [FinMatrix github](https://github.com/zhengpushi/FinMatrix), then
	`make; make install`
