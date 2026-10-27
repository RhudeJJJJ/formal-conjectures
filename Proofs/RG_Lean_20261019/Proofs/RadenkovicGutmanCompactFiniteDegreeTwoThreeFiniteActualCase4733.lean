/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4733 : Family 10 := level10.get ⟨960,by decide⟩
def sourceMap4733 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4733 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4733_checked : acceptsGraphIso
    (source (graph core4733) (root 10) 2 2) DegreeTwoThreeSpectrum7517.graph sourceMap4733=true := by decide +kernel
theorem fusedMap4733_checked : acceptsGraphIso
    (fused (graph core4733) (root 10) 2 2) DegreeTwoThreeSpectrum5869.graph fusedMap4733=true := by decide +kernel
theorem certified4733 : Certified (graph core4733) (root 10) 2 2 :=
  of_native_maps core4733 DegreeTwoThreeSpectrum7517.graph DegreeTwoThreeSpectrum5869.graph
    sourceMap4733 fusedMap4733 sourceMap4733_checked fusedMap4733_checked
    DegreeTwoThreeFiniteComparisons.comparison4733
#print axioms sourceMap4733_checked
#print axioms fusedMap4733_checked
#print axioms certified4733
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
