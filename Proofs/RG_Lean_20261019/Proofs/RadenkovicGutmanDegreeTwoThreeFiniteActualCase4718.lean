/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4718 : Family 10 := level10.get ⟨920,by decide⟩
def sourceMap4718 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4718 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4718_checked : acceptsGraphIso
    (source (graph core4718) (root 10) 2 2) DegreeTwoThreeSpectrum7489.graph sourceMap4718=true := by decide +kernel
theorem fusedMap4718_checked : acceptsGraphIso
    (fused (graph core4718) (root 10) 2 2) DegreeTwoThreeSpectrum5799.graph fusedMap4718=true := by decide +kernel
theorem certified4718 : Certified (graph core4718) (root 10) 2 2 :=
  of_native_maps core4718 DegreeTwoThreeSpectrum7489.graph DegreeTwoThreeSpectrum5799.graph
    sourceMap4718 fusedMap4718 sourceMap4718_checked fusedMap4718_checked
    DegreeTwoThreeFiniteComparisons.comparison4718
#print axioms sourceMap4718_checked
#print axioms fusedMap4718_checked
#print axioms certified4718
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
