This branch (stable) includes the Coq proof development accompanying the paper 
"A Role for Dependent Types in Haskell", conditionally accepted to ICFP 2019.

The prior development, corresponding to the ICFP 2017 paper, is available on 
the "master" branch. 

- [src](src/FcEtt) for Coq development.

- [spec](spec/ett.ott) for [Ott](http://www.cl.cam.ac.uk/~pes20/ott/) specification.

- [doc](doc/) for ICFP 17 paper "A Specification for Dependent Types in
Haskell".

- Added three new .v files. ett_path for reasoning about paths, ett_match for
  reasoning about match and substitute, ett_rename for reasoning about rename.
