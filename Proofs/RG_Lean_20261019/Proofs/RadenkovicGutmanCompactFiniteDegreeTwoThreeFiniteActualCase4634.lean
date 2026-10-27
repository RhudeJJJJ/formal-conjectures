/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4634 : Family 10 := level10.get ⟨697,by decide⟩
def sourceMap4634 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4634 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4634_checked : acceptsGraphIso
    (source (graph core4634) (root 10) 2 2) DegreeTwoThreeSpectrum7350.graph sourceMap4634=true := by decide +kernel
theorem fusedMap4634_checked : acceptsGraphIso
    (fused (graph core4634) (root 10) 2 2) DegreeTwoThreeSpectrum5434.graph fusedMap4634=true := by decide +kernel
theorem certified4634 : Certified (graph core4634) (root 10) 2 2 :=
  of_native_maps core4634 DegreeTwoThreeSpectrum7350.graph DegreeTwoThreeSpectrum5434.graph
    sourceMap4634 fusedMap4634 sourceMap4634_checked fusedMap4634_checked
    DegreeTwoThreeFiniteComparisons.comparison4634
#print axioms sourceMap4634_checked
#print axioms fusedMap4634_checked
#print axioms certified4634
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
