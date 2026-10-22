/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4654 : Family 10 := level10.get ⟨756,by decide⟩
def sourceMap4654 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4654 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4654_checked : acceptsGraphIso
    (source (graph core4654) (root 10) 2 2) DegreeTwoThreeSpectrum7422.graph sourceMap4654=true := by decide +kernel
theorem fusedMap4654_checked : acceptsGraphIso
    (fused (graph core4654) (root 10) 2 2) DegreeTwoThreeSpectrum5522.graph fusedMap4654=true := by decide +kernel
theorem certified4654 : Certified (graph core4654) (root 10) 2 2 :=
  of_native_maps core4654 DegreeTwoThreeSpectrum7422.graph DegreeTwoThreeSpectrum5522.graph
    sourceMap4654 fusedMap4654 sourceMap4654_checked fusedMap4654_checked
    DegreeTwoThreeFiniteComparisons.comparison4654
#print axioms sourceMap4654_checked
#print axioms fusedMap4654_checked
#print axioms certified4654
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
