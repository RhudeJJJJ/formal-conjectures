/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4740 : Family 10 := level10.get ⟨975,by decide⟩
def sourceMap4740 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4740 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4740_checked : acceptsGraphIso
    (source (graph core4740) (root 10) 2 2) DegreeTwoThreeSpectrum7052.graph sourceMap4740=true := by decide +kernel
theorem fusedMap4740_checked : acceptsGraphIso
    (fused (graph core4740) (root 10) 2 2) DegreeTwoThreeSpectrum5909.graph fusedMap4740=true := by decide +kernel
theorem certified4740 : Certified (graph core4740) (root 10) 2 2 :=
  of_native_maps core4740 DegreeTwoThreeSpectrum7052.graph DegreeTwoThreeSpectrum5909.graph
    sourceMap4740 fusedMap4740 sourceMap4740_checked fusedMap4740_checked
    DegreeTwoThreeFiniteComparisons.comparison4740
#print axioms sourceMap4740_checked
#print axioms fusedMap4740_checked
#print axioms certified4740
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
