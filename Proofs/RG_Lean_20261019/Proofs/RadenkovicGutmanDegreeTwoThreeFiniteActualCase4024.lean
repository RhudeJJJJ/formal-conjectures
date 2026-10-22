/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4024 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap4024 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4024 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4024_checked : acceptsGraphIso
    (source (graph core4024) (root 5) 1 7) DegreeTwoThreeSpectrum4268.graph sourceMap4024=true := by decide +kernel
theorem fusedMap4024_checked : acceptsGraphIso
    (fused (graph core4024) (root 5) 1 7) DegreeTwoThreeSpectrum3922.graph fusedMap4024=true := by decide +kernel
theorem certified4024 : Certified (graph core4024) (root 5) 1 7 :=
  of_native_maps core4024 DegreeTwoThreeSpectrum4268.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap4024 fusedMap4024 sourceMap4024_checked fusedMap4024_checked
    DegreeTwoThreeFiniteComparisons.comparison4024
#print axioms sourceMap4024_checked
#print axioms fusedMap4024_checked
#print axioms certified4024
def sourceMap4024swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,11,12,13,14,15,9,10] (sourceLabel 5 7 1 v)
def fusedMap4024swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4024swap_checked : acceptsGraphIso
    (source (graph core4024) (root 5) 7 1) DegreeTwoThreeSpectrum4268.graph sourceMap4024swap=true := by decide +kernel
theorem fusedMap4024swap_checked : acceptsGraphIso
    (fused (graph core4024) (root 5) 7 1) DegreeTwoThreeSpectrum3922.graph fusedMap4024swap=true := by decide +kernel
theorem certified4024swap : Certified (graph core4024) (root 5) 7 1 :=
  of_native_maps core4024 DegreeTwoThreeSpectrum4268.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap4024swap fusedMap4024swap sourceMap4024swap_checked fusedMap4024swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4024
#print axioms sourceMap4024swap_checked
#print axioms fusedMap4024swap_checked
#print axioms certified4024swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
