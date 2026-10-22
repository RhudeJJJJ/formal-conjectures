/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4749 : Family 10 := level10.get ⟨998,by decide⟩
def sourceMap4749 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4749 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4749_checked : acceptsGraphIso
    (source (graph core4749) (root 10) 2 2) DegreeTwoThreeSpectrum7068.graph sourceMap4749=true := by decide +kernel
theorem fusedMap4749_checked : acceptsGraphIso
    (fused (graph core4749) (root 10) 2 2) DegreeTwoThreeSpectrum5970.graph fusedMap4749=true := by decide +kernel
theorem certified4749 : Certified (graph core4749) (root 10) 2 2 :=
  of_native_maps core4749 DegreeTwoThreeSpectrum7068.graph DegreeTwoThreeSpectrum5970.graph
    sourceMap4749 fusedMap4749 sourceMap4749_checked fusedMap4749_checked
    DegreeTwoThreeFiniteComparisons.comparison4749
#print axioms sourceMap4749_checked
#print axioms fusedMap4749_checked
#print axioms certified4749
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
