/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4861 : Family 10 := level10.get ⟨1281,by decide⟩
def sourceMap4861 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4861 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4861_checked : acceptsGraphIso
    (source (graph core4861) (root 10) 2 2) DegreeTwoThreeSpectrum7363.graph sourceMap4861=true := by decide +kernel
theorem fusedMap4861_checked : acceptsGraphIso
    (fused (graph core4861) (root 10) 2 2) DegreeTwoThreeSpectrum6547.graph fusedMap4861=true := by decide +kernel
theorem certified4861 : Certified (graph core4861) (root 10) 2 2 :=
  of_native_maps core4861 DegreeTwoThreeSpectrum7363.graph DegreeTwoThreeSpectrum6547.graph
    sourceMap4861 fusedMap4861 sourceMap4861_checked fusedMap4861_checked
    DegreeTwoThreeFiniteComparisons.comparison4861
#print axioms sourceMap4861_checked
#print axioms fusedMap4861_checked
#print axioms certified4861
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
