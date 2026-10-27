/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4705 : Family 10 := level10.get ⟨891,by decide⟩
def sourceMap4705 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4705 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4705_checked : acceptsGraphIso
    (source (graph core4705) (root 10) 2 2) DegreeTwoThreeSpectrum7480.graph sourceMap4705=true := by decide +kernel
theorem fusedMap4705_checked : acceptsGraphIso
    (fused (graph core4705) (root 10) 2 2) DegreeTwoThreeSpectrum5749.graph fusedMap4705=true := by decide +kernel
theorem certified4705 : Certified (graph core4705) (root 10) 2 2 :=
  of_native_maps core4705 DegreeTwoThreeSpectrum7480.graph DegreeTwoThreeSpectrum5749.graph
    sourceMap4705 fusedMap4705 sourceMap4705_checked fusedMap4705_checked
    DegreeTwoThreeFiniteComparisons.comparison4705
#print axioms sourceMap4705_checked
#print axioms fusedMap4705_checked
#print axioms certified4705
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
