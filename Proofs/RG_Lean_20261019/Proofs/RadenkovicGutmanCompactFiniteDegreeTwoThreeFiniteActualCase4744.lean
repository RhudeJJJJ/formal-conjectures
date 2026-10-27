/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4744 : Family 10 := level10.get ⟨980,by decide⟩
def sourceMap4744 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,13,14,15,16,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4744 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4744_checked : acceptsGraphIso
    (source (graph core4744) (root 10) 2 2) DegreeTwoThreeSpectrum7150.graph sourceMap4744=true := by decide +kernel
theorem fusedMap4744_checked : acceptsGraphIso
    (fused (graph core4744) (root 10) 2 2) DegreeTwoThreeSpectrum5915.graph fusedMap4744=true := by decide +kernel
theorem certified4744 : Certified (graph core4744) (root 10) 2 2 :=
  of_native_maps core4744 DegreeTwoThreeSpectrum7150.graph DegreeTwoThreeSpectrum5915.graph
    sourceMap4744 fusedMap4744 sourceMap4744_checked fusedMap4744_checked
    DegreeTwoThreeFiniteComparisons.comparison4744
#print axioms sourceMap4744_checked
#print axioms fusedMap4744_checked
#print axioms certified4744
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
