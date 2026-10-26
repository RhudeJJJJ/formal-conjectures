/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3611 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap3611 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3611 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3611_checked : acceptsGraphIso
    (source (graph core3611) (root 8) 0 6) DegreeTwoThreeSpectrum6220.graph sourceMap3611=true := by decide +kernel
theorem fusedMap3611_checked : acceptsGraphIso
    (fused (graph core3611) (root 8) 0 6) DegreeTwoThreeSpectrum5233.graph fusedMap3611=true := by decide +kernel
theorem certified3611 : Certified (graph core3611) (root 8) 0 6 :=
  of_native_maps core3611 DegreeTwoThreeSpectrum6220.graph DegreeTwoThreeSpectrum5233.graph
    sourceMap3611 fusedMap3611 sourceMap3611_checked fusedMap3611_checked
    DegreeTwoThreeFiniteComparisons.comparison3611
#print axioms sourceMap3611_checked
#print axioms fusedMap3611_checked
#print axioms certified3611
def sourceMap3611swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3611swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3611swap_checked : acceptsGraphIso
    (source (graph core3611) (root 8) 6 0) DegreeTwoThreeSpectrum6220.graph sourceMap3611swap=true := by decide +kernel
theorem fusedMap3611swap_checked : acceptsGraphIso
    (fused (graph core3611) (root 8) 6 0) DegreeTwoThreeSpectrum5233.graph fusedMap3611swap=true := by decide +kernel
theorem certified3611swap : Certified (graph core3611) (root 8) 6 0 :=
  of_native_maps core3611 DegreeTwoThreeSpectrum6220.graph DegreeTwoThreeSpectrum5233.graph
    sourceMap3611swap fusedMap3611swap sourceMap3611swap_checked fusedMap3611swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3611
#print axioms sourceMap3611swap_checked
#print axioms fusedMap3611swap_checked
#print axioms certified3611swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
