/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4690 : Family 10 := level10.get ⟨854,by decide⟩
def sourceMap4690 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4690 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4690_checked : acceptsGraphIso
    (source (graph core4690) (root 10) 2 2) DegreeTwoThreeSpectrum7529.graph sourceMap4690=true := by decide +kernel
theorem fusedMap4690_checked : acceptsGraphIso
    (fused (graph core4690) (root 10) 2 2) DegreeTwoThreeSpectrum5690.graph fusedMap4690=true := by decide +kernel
theorem certified4690 : Certified (graph core4690) (root 10) 2 2 :=
  of_native_maps core4690 DegreeTwoThreeSpectrum7529.graph DegreeTwoThreeSpectrum5690.graph
    sourceMap4690 fusedMap4690 sourceMap4690_checked fusedMap4690_checked
    DegreeTwoThreeFiniteComparisons.comparison4690
#print axioms sourceMap4690_checked
#print axioms fusedMap4690_checked
#print axioms certified4690
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
