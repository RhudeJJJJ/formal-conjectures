/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3484 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3484 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3484 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3484_checked : acceptsGraphIso
    (source (graph core3484) (root 5) 0 6) DegreeTwoThreeSpectrum1743.graph sourceMap3484=true := by decide +kernel
theorem fusedMap3484_checked : acceptsGraphIso
    (fused (graph core3484) (root 5) 0 6) DegreeTwoThreeSpectrum1746.graph fusedMap3484=true := by decide +kernel
theorem certified3484 : Certified (graph core3484) (root 5) 0 6 :=
  of_native_maps core3484 DegreeTwoThreeSpectrum1743.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap3484 fusedMap3484 sourceMap3484_checked fusedMap3484_checked
    DegreeTwoThreeFiniteComparisons.comparison3484
#print axioms sourceMap3484_checked
#print axioms fusedMap3484_checked
#print axioms certified3484
def sourceMap3484swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,8] (sourceLabel 5 6 0 v)
def fusedMap3484swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3484swap_checked : acceptsGraphIso
    (source (graph core3484) (root 5) 6 0) DegreeTwoThreeSpectrum1743.graph sourceMap3484swap=true := by decide +kernel
theorem fusedMap3484swap_checked : acceptsGraphIso
    (fused (graph core3484) (root 5) 6 0) DegreeTwoThreeSpectrum1746.graph fusedMap3484swap=true := by decide +kernel
theorem certified3484swap : Certified (graph core3484) (root 5) 6 0 :=
  of_native_maps core3484 DegreeTwoThreeSpectrum1743.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap3484swap fusedMap3484swap sourceMap3484swap_checked fusedMap3484swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3484
#print axioms sourceMap3484swap_checked
#print axioms fusedMap3484swap_checked
#print axioms certified3484swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
