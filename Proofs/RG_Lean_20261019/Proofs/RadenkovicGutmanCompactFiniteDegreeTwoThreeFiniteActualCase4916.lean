/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4916 : Family 10 := level10.get ⟨1410,by decide⟩
def sourceMap4916 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4916 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4916_checked : acceptsGraphIso
    (source (graph core4916) (root 10) 2 2) DegreeTwoThreeSpectrum7518.graph sourceMap4916=true := by decide +kernel
theorem fusedMap4916_checked : acceptsGraphIso
    (fused (graph core4916) (root 10) 2 2) DegreeTwoThreeSpectrum6818.graph fusedMap4916=true := by decide +kernel
theorem certified4916 : Certified (graph core4916) (root 10) 2 2 :=
  of_native_maps core4916 DegreeTwoThreeSpectrum7518.graph DegreeTwoThreeSpectrum6818.graph
    sourceMap4916 fusedMap4916 sourceMap4916_checked fusedMap4916_checked
    DegreeTwoThreeFiniteComparisons.comparison4916
#print axioms sourceMap4916_checked
#print axioms fusedMap4916_checked
#print axioms certified4916
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
