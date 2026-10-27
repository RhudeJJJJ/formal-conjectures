/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4717 : Family 10 := level10.get ⟨918,by decide⟩
def sourceMap4717 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4717 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4717_checked : acceptsGraphIso
    (source (graph core4717) (root 10) 2 2) DegreeTwoThreeSpectrum7430.graph sourceMap4717=true := by decide +kernel
theorem fusedMap4717_checked : acceptsGraphIso
    (fused (graph core4717) (root 10) 2 2) DegreeTwoThreeSpectrum5796.graph fusedMap4717=true := by decide +kernel
theorem certified4717 : Certified (graph core4717) (root 10) 2 2 :=
  of_native_maps core4717 DegreeTwoThreeSpectrum7430.graph DegreeTwoThreeSpectrum5796.graph
    sourceMap4717 fusedMap4717 sourceMap4717_checked fusedMap4717_checked
    DegreeTwoThreeFiniteComparisons.comparison4717
#print axioms sourceMap4717_checked
#print axioms fusedMap4717_checked
#print axioms certified4717
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
