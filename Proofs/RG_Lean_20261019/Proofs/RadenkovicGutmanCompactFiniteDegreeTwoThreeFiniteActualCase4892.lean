/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4892 : Family 10 := level10.get ⟨1354,by decide⟩
def sourceMap4892 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4892 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4892_checked : acceptsGraphIso
    (source (graph core4892) (root 10) 2 2) DegreeTwoThreeSpectrum7437.graph sourceMap4892=true := by decide +kernel
theorem fusedMap4892_checked : acceptsGraphIso
    (fused (graph core4892) (root 10) 2 2) DegreeTwoThreeSpectrum6690.graph fusedMap4892=true := by decide +kernel
theorem certified4892 : Certified (graph core4892) (root 10) 2 2 :=
  of_native_maps core4892 DegreeTwoThreeSpectrum7437.graph DegreeTwoThreeSpectrum6690.graph
    sourceMap4892 fusedMap4892 sourceMap4892_checked fusedMap4892_checked
    DegreeTwoThreeFiniteComparisons.comparison4892
#print axioms sourceMap4892_checked
#print axioms fusedMap4892_checked
#print axioms certified4892
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
