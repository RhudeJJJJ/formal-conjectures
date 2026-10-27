/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4849 : Family 10 := level10.get ⟨1251,by decide⟩
def sourceMap4849 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4849 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4849_checked : acceptsGraphIso
    (source (graph core4849) (root 10) 2 2) DegreeTwoThreeSpectrum7333.graph sourceMap4849=true := by decide +kernel
theorem fusedMap4849_checked : acceptsGraphIso
    (fused (graph core4849) (root 10) 2 2) DegreeTwoThreeSpectrum6491.graph fusedMap4849=true := by decide +kernel
theorem certified4849 : Certified (graph core4849) (root 10) 2 2 :=
  of_native_maps core4849 DegreeTwoThreeSpectrum7333.graph DegreeTwoThreeSpectrum6491.graph
    sourceMap4849 fusedMap4849 sourceMap4849_checked fusedMap4849_checked
    DegreeTwoThreeFiniteComparisons.comparison4849
#print axioms sourceMap4849_checked
#print axioms fusedMap4849_checked
#print axioms certified4849
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
