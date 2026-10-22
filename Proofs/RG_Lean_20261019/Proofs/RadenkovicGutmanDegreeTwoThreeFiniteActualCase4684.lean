/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4684 : Family 10 := level10.get ⟨836,by decide⟩
def sourceMap4684 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4684 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4684_checked : acceptsGraphIso
    (source (graph core4684) (root 10) 2 2) DegreeTwoThreeSpectrum7520.graph sourceMap4684=true := by decide +kernel
theorem fusedMap4684_checked : acceptsGraphIso
    (fused (graph core4684) (root 10) 2 2) DegreeTwoThreeSpectrum5664.graph fusedMap4684=true := by decide +kernel
theorem certified4684 : Certified (graph core4684) (root 10) 2 2 :=
  of_native_maps core4684 DegreeTwoThreeSpectrum7520.graph DegreeTwoThreeSpectrum5664.graph
    sourceMap4684 fusedMap4684 sourceMap4684_checked fusedMap4684_checked
    DegreeTwoThreeFiniteComparisons.comparison4684
#print axioms sourceMap4684_checked
#print axioms fusedMap4684_checked
#print axioms certified4684
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
