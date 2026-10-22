/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2893 : Family 10 := level10.get ⟨1303,by decide⟩
def sourceMap2893 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2893 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2893_checked : acceptsGraphIso
    (source (graph core2893) (root 10) 0 4) DegreeTwoThreeSpectrum6593.graph sourceMap2893=true := by decide +kernel
theorem fusedMap2893_checked : acceptsGraphIso
    (fused (graph core2893) (root 10) 0 4) DegreeTwoThreeSpectrum6594.graph fusedMap2893=true := by decide +kernel
theorem certified2893 : Certified (graph core2893) (root 10) 0 4 :=
  of_native_maps core2893 DegreeTwoThreeSpectrum6593.graph DegreeTwoThreeSpectrum6594.graph
    sourceMap2893 fusedMap2893 sourceMap2893_checked fusedMap2893_checked
    DegreeTwoThreeFiniteComparisons.comparison2893
#print axioms sourceMap2893_checked
#print axioms fusedMap2893_checked
#print axioms certified2893
def sourceMap2893swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2893swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2893swap_checked : acceptsGraphIso
    (source (graph core2893) (root 10) 4 0) DegreeTwoThreeSpectrum6593.graph sourceMap2893swap=true := by decide +kernel
theorem fusedMap2893swap_checked : acceptsGraphIso
    (fused (graph core2893) (root 10) 4 0) DegreeTwoThreeSpectrum6594.graph fusedMap2893swap=true := by decide +kernel
theorem certified2893swap : Certified (graph core2893) (root 10) 4 0 :=
  of_native_maps core2893 DegreeTwoThreeSpectrum6593.graph DegreeTwoThreeSpectrum6594.graph
    sourceMap2893swap fusedMap2893swap sourceMap2893swap_checked fusedMap2893swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2893
#print axioms sourceMap2893swap_checked
#print axioms fusedMap2893swap_checked
#print axioms certified2893swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
