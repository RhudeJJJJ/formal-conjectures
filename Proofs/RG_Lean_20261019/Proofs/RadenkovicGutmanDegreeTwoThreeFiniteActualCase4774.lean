/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4774 : Family 10 := level10.get ⟨1068,by decide⟩
def sourceMap4774 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4774 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4774_checked : acceptsGraphIso
    (source (graph core4774) (root 10) 2 2) DegreeTwoThreeSpectrum7152.graph sourceMap4774=true := by decide +kernel
theorem fusedMap4774_checked : acceptsGraphIso
    (fused (graph core4774) (root 10) 2 2) DegreeTwoThreeSpectrum6125.graph fusedMap4774=true := by decide +kernel
theorem certified4774 : Certified (graph core4774) (root 10) 2 2 :=
  of_native_maps core4774 DegreeTwoThreeSpectrum7152.graph DegreeTwoThreeSpectrum6125.graph
    sourceMap4774 fusedMap4774 sourceMap4774_checked fusedMap4774_checked
    DegreeTwoThreeFiniteComparisons.comparison4774
#print axioms sourceMap4774_checked
#print axioms fusedMap4774_checked
#print axioms certified4774
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
