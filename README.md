# Cryptanalysis_SNOVA_Multihomogeneous

This repository contains the Magma codes used for experiments presented in the paper:

> **"Improved Cryptanalysis of SNOVA by Solving　Multi-homogeneous Systems via Matrix Transformations"**  
> Hiroki Furue, Yasuhiko Ikematsu, Shuhei Nakamura, Rika Akiyama  
> ASIACRYPT 2025  

---

## 🧩 Modules Overview

| File Name                   | Description                                                                          |
|-----------------------------|--------------------------------------------------------------------------------------|
| `intersection_experiment.m` | Computes the rank of the Macaulay matrix in the intersection attack (Table 2)        |
| `intersection_complexity.m` | Estimates the complexity of the intersection attack (Table 3)                        |
| `rectangular_experiment.m`  | Computes the rank of the Macaulay matrix in the rectangular MinRank attack (Table 5) |
| `rectangular_complexity.m`  | Estimates the complexity of the rectangular MinRank attack (Table 4)                 |
