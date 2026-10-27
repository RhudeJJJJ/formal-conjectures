/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4709 : Family 10 := level10.get ⟨905,by decide⟩
def sourceMap4709 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4709 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4709_checked : acceptsGraphIso
    (source (graph core4709) (root 10) 2 2) DegreeTwoThreeSpectrum7542.graph sourceMap4709=true := by decide +kernel
theorem fusedMap4709_checked : acceptsGraphIso
    (fused (graph core4709) (root 10) 2 2) DegreeTwoThreeSpectrum5770.graph fusedMap4709=true := by decide +kernel
theorem certified4709 : Certified (graph core4709) (root 10) 2 2 :=
  of_native_maps core4709 DegreeTwoThreeSpectrum7542.graph DegreeTwoThreeSpectrum5770.graph
    sourceMap4709 fusedMap4709 sourceMap4709_checked fusedMap4709_checked
    DegreeTwoThreeFiniteComparisons.comparison4709
#print axioms sourceMap4709_checked
#print axioms fusedMap4709_checked
#print axioms certified4709
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
