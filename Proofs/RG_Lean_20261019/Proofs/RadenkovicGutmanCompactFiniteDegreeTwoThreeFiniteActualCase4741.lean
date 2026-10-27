/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4741 : Family 10 := level10.get ⟨976,by decide⟩
def sourceMap4741 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4741 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4741_checked : acceptsGraphIso
    (source (graph core4741) (root 10) 2 2) DegreeTwoThreeSpectrum6435.graph sourceMap4741=true := by decide +kernel
theorem fusedMap4741_checked : acceptsGraphIso
    (fused (graph core4741) (root 10) 2 2) DegreeTwoThreeSpectrum5910.graph fusedMap4741=true := by decide +kernel
theorem certified4741 : Certified (graph core4741) (root 10) 2 2 :=
  of_native_maps core4741 DegreeTwoThreeSpectrum6435.graph DegreeTwoThreeSpectrum5910.graph
    sourceMap4741 fusedMap4741 sourceMap4741_checked fusedMap4741_checked
    DegreeTwoThreeFiniteComparisons.comparison4741
#print axioms sourceMap4741_checked
#print axioms fusedMap4741_checked
#print axioms certified4741
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
