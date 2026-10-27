/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4675 : Family 10 := level10.get ⟨814,by decide⟩
def sourceMap4675 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4675 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4675_checked : acceptsGraphIso
    (source (graph core4675) (root 10) 2 2) DegreeTwoThreeSpectrum7473.graph sourceMap4675=true := by decide +kernel
theorem fusedMap4675_checked : acceptsGraphIso
    (fused (graph core4675) (root 10) 2 2) DegreeTwoThreeSpectrum5613.graph fusedMap4675=true := by decide +kernel
theorem certified4675 : Certified (graph core4675) (root 10) 2 2 :=
  of_native_maps core4675 DegreeTwoThreeSpectrum7473.graph DegreeTwoThreeSpectrum5613.graph
    sourceMap4675 fusedMap4675 sourceMap4675_checked fusedMap4675_checked
    DegreeTwoThreeFiniteComparisons.comparison4675
#print axioms sourceMap4675_checked
#print axioms fusedMap4675_checked
#print axioms certified4675
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
