/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4600 : Family 10 := level10.get ⟨601,by decide⟩
def sourceMap4600 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4600 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4600_checked : acceptsGraphIso
    (source (graph core4600) (root 10) 2 2) DegreeTwoThreeSpectrum7247.graph sourceMap4600=true := by decide +kernel
theorem fusedMap4600_checked : acceptsGraphIso
    (fused (graph core4600) (root 10) 2 2) DegreeTwoThreeSpectrum5277.graph fusedMap4600=true := by decide +kernel
theorem certified4600 : Certified (graph core4600) (root 10) 2 2 :=
  of_native_maps core4600 DegreeTwoThreeSpectrum7247.graph DegreeTwoThreeSpectrum5277.graph
    sourceMap4600 fusedMap4600 sourceMap4600_checked fusedMap4600_checked
    DegreeTwoThreeFiniteComparisons.comparison4600
#print axioms sourceMap4600_checked
#print axioms fusedMap4600_checked
#print axioms certified4600
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
