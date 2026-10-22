/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4581 : Family 10 := level10.get ⟨544,by decide⟩
def sourceMap4581 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4581 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4581_checked : acceptsGraphIso
    (source (graph core4581) (root 10) 2 2) DegreeTwoThreeSpectrum7164.graph sourceMap4581=true := by decide +kernel
theorem fusedMap4581_checked : acceptsGraphIso
    (fused (graph core4581) (root 10) 2 2) DegreeTwoThreeSpectrum5194.graph fusedMap4581=true := by decide +kernel
theorem certified4581 : Certified (graph core4581) (root 10) 2 2 :=
  of_native_maps core4581 DegreeTwoThreeSpectrum7164.graph DegreeTwoThreeSpectrum5194.graph
    sourceMap4581 fusedMap4581 sourceMap4581_checked fusedMap4581_checked
    DegreeTwoThreeFiniteComparisons.comparison4581
#print axioms sourceMap4581_checked
#print axioms fusedMap4581_checked
#print axioms certified4581
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
