/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4747 : Family 10 := level10.get ⟨984,by decide⟩
def sourceMap4747 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,13,14,15,16,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4747 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4747_checked : acceptsGraphIso
    (source (graph core4747) (root 10) 2 2) DegreeTwoThreeSpectrum7401.graph sourceMap4747=true := by decide +kernel
theorem fusedMap4747_checked : acceptsGraphIso
    (fused (graph core4747) (root 10) 2 2) DegreeTwoThreeSpectrum5920.graph fusedMap4747=true := by decide +kernel
theorem certified4747 : Certified (graph core4747) (root 10) 2 2 :=
  of_native_maps core4747 DegreeTwoThreeSpectrum7401.graph DegreeTwoThreeSpectrum5920.graph
    sourceMap4747 fusedMap4747 sourceMap4747_checked fusedMap4747_checked
    DegreeTwoThreeFiniteComparisons.comparison4747
#print axioms sourceMap4747_checked
#print axioms fusedMap4747_checked
#print axioms certified4747
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
