/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4707 : Family 10 := level10.get ⟨899,by decide⟩
def sourceMap4707 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4707 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4707_checked : acceptsGraphIso
    (source (graph core4707) (root 10) 2 2) DegreeTwoThreeSpectrum7540.graph sourceMap4707=true := by decide +kernel
theorem fusedMap4707_checked : acceptsGraphIso
    (fused (graph core4707) (root 10) 2 2) DegreeTwoThreeSpectrum5764.graph fusedMap4707=true := by decide +kernel
theorem certified4707 : Certified (graph core4707) (root 10) 2 2 :=
  of_native_maps core4707 DegreeTwoThreeSpectrum7540.graph DegreeTwoThreeSpectrum5764.graph
    sourceMap4707 fusedMap4707 sourceMap4707_checked fusedMap4707_checked
    DegreeTwoThreeFiniteComparisons.comparison4707
#print axioms sourceMap4707_checked
#print axioms fusedMap4707_checked
#print axioms certified4707
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
