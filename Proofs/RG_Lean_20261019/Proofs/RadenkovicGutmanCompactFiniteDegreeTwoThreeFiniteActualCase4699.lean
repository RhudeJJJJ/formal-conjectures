/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4699 : Family 10 := level10.get ⟨877,by decide⟩
def sourceMap4699 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4699 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4699_checked : acceptsGraphIso
    (source (graph core4699) (root 10) 2 2) DegreeTwoThreeSpectrum7536.graph sourceMap4699=true := by decide +kernel
theorem fusedMap4699_checked : acceptsGraphIso
    (fused (graph core4699) (root 10) 2 2) DegreeTwoThreeSpectrum5727.graph fusedMap4699=true := by decide +kernel
theorem certified4699 : Certified (graph core4699) (root 10) 2 2 :=
  of_native_maps core4699 DegreeTwoThreeSpectrum7536.graph DegreeTwoThreeSpectrum5727.graph
    sourceMap4699 fusedMap4699 sourceMap4699_checked fusedMap4699_checked
    DegreeTwoThreeFiniteComparisons.comparison4699
#print axioms sourceMap4699_checked
#print axioms fusedMap4699_checked
#print axioms certified4699
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
