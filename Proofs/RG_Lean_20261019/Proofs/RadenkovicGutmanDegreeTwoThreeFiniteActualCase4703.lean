/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4703 : Family 10 := level10.get ⟨888,by decide⟩
def sourceMap4703 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4703 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4703_checked : acceptsGraphIso
    (source (graph core4703) (root 10) 2 2) DegreeTwoThreeSpectrum7539.graph sourceMap4703=true := by decide +kernel
theorem fusedMap4703_checked : acceptsGraphIso
    (fused (graph core4703) (root 10) 2 2) DegreeTwoThreeSpectrum5742.graph fusedMap4703=true := by decide +kernel
theorem certified4703 : Certified (graph core4703) (root 10) 2 2 :=
  of_native_maps core4703 DegreeTwoThreeSpectrum7539.graph DegreeTwoThreeSpectrum5742.graph
    sourceMap4703 fusedMap4703 sourceMap4703_checked fusedMap4703_checked
    DegreeTwoThreeFiniteComparisons.comparison4703
#print axioms sourceMap4703_checked
#print axioms fusedMap4703_checked
#print axioms certified4703
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
