/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4682 : Family 10 := level10.get ⟨825,by decide⟩
def sourceMap4682 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4682 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4682_checked : acceptsGraphIso
    (source (graph core4682) (root 10) 2 2) DegreeTwoThreeSpectrum7466.graph sourceMap4682=true := by decide +kernel
theorem fusedMap4682_checked : acceptsGraphIso
    (fused (graph core4682) (root 10) 2 2) DegreeTwoThreeSpectrum5635.graph fusedMap4682=true := by decide +kernel
theorem certified4682 : Certified (graph core4682) (root 10) 2 2 :=
  of_native_maps core4682 DegreeTwoThreeSpectrum7466.graph DegreeTwoThreeSpectrum5635.graph
    sourceMap4682 fusedMap4682 sourceMap4682_checked fusedMap4682_checked
    DegreeTwoThreeFiniteComparisons.comparison4682
#print axioms sourceMap4682_checked
#print axioms fusedMap4682_checked
#print axioms certified4682
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
