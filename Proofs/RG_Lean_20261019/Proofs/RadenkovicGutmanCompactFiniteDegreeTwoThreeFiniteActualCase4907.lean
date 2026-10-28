/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4907 : Family 10 := level10.get ⟨1382,by decide⟩
def sourceMap4907 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4907 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4907_checked : acceptsGraphIso
    (source (graph core4907) (root 10) 2 2) DegreeTwoThreeSpectrum7457.graph sourceMap4907=true := by decide +kernel
theorem fusedMap4907_checked : acceptsGraphIso
    (fused (graph core4907) (root 10) 2 2) DegreeTwoThreeSpectrum6736.graph fusedMap4907=true := by decide +kernel
theorem certified4907 : Certified (graph core4907) (root 10) 2 2 :=
  of_native_maps core4907 DegreeTwoThreeSpectrum7457.graph DegreeTwoThreeSpectrum6736.graph
    sourceMap4907 fusedMap4907 sourceMap4907_checked fusedMap4907_checked
    DegreeTwoThreeFiniteComparisons.comparison4907
#print axioms sourceMap4907_checked
#print axioms fusedMap4907_checked
#print axioms certified4907
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
