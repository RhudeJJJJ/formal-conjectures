/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4858 : Family 10 := level10.get ⟨1274,by decide⟩
def sourceMap4858 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4858 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4858_checked : acceptsGraphIso
    (source (graph core4858) (root 10) 2 2) DegreeTwoThreeSpectrum7359.graph sourceMap4858=true := by decide +kernel
theorem fusedMap4858_checked : acceptsGraphIso
    (fused (graph core4858) (root 10) 2 2) DegreeTwoThreeSpectrum6539.graph fusedMap4858=true := by decide +kernel
theorem certified4858 : Certified (graph core4858) (root 10) 2 2 :=
  of_native_maps core4858 DegreeTwoThreeSpectrum7359.graph DegreeTwoThreeSpectrum6539.graph
    sourceMap4858 fusedMap4858 sourceMap4858_checked fusedMap4858_checked
    DegreeTwoThreeFiniteComparisons.comparison4858
#print axioms sourceMap4858_checked
#print axioms fusedMap4858_checked
#print axioms certified4858
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
