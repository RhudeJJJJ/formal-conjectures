/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3932 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3932 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3932 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3932_checked : acceptsGraphIso
    (source (graph core3932) (root 5) 1 5) DegreeTwoThreeSpectrum1953.graph sourceMap3932=true := by decide +kernel
theorem fusedMap3932_checked : acceptsGraphIso
    (fused (graph core3932) (root 5) 1 5) DegreeTwoThreeSpectrum1746.graph fusedMap3932=true := by decide +kernel
theorem certified3932 : Certified (graph core3932) (root 5) 1 5 :=
  of_native_maps core3932 DegreeTwoThreeSpectrum1953.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap3932 fusedMap3932 sourceMap3932_checked fusedMap3932_checked
    DegreeTwoThreeFiniteComparisons.comparison3932
#print axioms sourceMap3932_checked
#print axioms fusedMap3932_checked
#print axioms certified3932
def sourceMap3932swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,7,8] (sourceLabel 5 5 1 v)
def fusedMap3932swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3932swap_checked : acceptsGraphIso
    (source (graph core3932) (root 5) 5 1) DegreeTwoThreeSpectrum1953.graph sourceMap3932swap=true := by decide +kernel
theorem fusedMap3932swap_checked : acceptsGraphIso
    (fused (graph core3932) (root 5) 5 1) DegreeTwoThreeSpectrum1746.graph fusedMap3932swap=true := by decide +kernel
theorem certified3932swap : Certified (graph core3932) (root 5) 5 1 :=
  of_native_maps core3932 DegreeTwoThreeSpectrum1953.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap3932swap fusedMap3932swap sourceMap3932swap_checked fusedMap3932swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3932
#print axioms sourceMap3932swap_checked
#print axioms fusedMap3932swap_checked
#print axioms certified3932swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
