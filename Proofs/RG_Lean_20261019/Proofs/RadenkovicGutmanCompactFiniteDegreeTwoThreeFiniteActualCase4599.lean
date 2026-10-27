/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4599 : Family 10 := level10.get ⟨600,by decide⟩
def sourceMap4599 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4599 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4599_checked : acceptsGraphIso
    (source (graph core4599) (root 10) 2 2) DegreeTwoThreeSpectrum7248.graph sourceMap4599=true := by decide +kernel
theorem fusedMap4599_checked : acceptsGraphIso
    (fused (graph core4599) (root 10) 2 2) DegreeTwoThreeSpectrum5275.graph fusedMap4599=true := by decide +kernel
theorem certified4599 : Certified (graph core4599) (root 10) 2 2 :=
  of_native_maps core4599 DegreeTwoThreeSpectrum7248.graph DegreeTwoThreeSpectrum5275.graph
    sourceMap4599 fusedMap4599 sourceMap4599_checked fusedMap4599_checked
    DegreeTwoThreeFiniteComparisons.comparison4599
#print axioms sourceMap4599_checked
#print axioms fusedMap4599_checked
#print axioms certified4599
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
