/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4628 : Family 10 := level10.get ⟨675,by decide⟩
def sourceMap4628 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4628 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4628_checked : acceptsGraphIso
    (source (graph core4628) (root 10) 2 2) DegreeTwoThreeSpectrum7265.graph sourceMap4628=true := by decide +kernel
theorem fusedMap4628_checked : acceptsGraphIso
    (fused (graph core4628) (root 10) 2 2) DegreeTwoThreeSpectrum5397.graph fusedMap4628=true := by decide +kernel
theorem certified4628 : Certified (graph core4628) (root 10) 2 2 :=
  of_native_maps core4628 DegreeTwoThreeSpectrum7265.graph DegreeTwoThreeSpectrum5397.graph
    sourceMap4628 fusedMap4628 sourceMap4628_checked fusedMap4628_checked
    DegreeTwoThreeFiniteComparisons.comparison4628
#print axioms sourceMap4628_checked
#print axioms fusedMap4628_checked
#print axioms certified4628
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
