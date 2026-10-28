/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4949 : Family 10 := level10.get ⟨1480,by decide⟩
def sourceMap4949 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4949 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4949_checked : acceptsGraphIso
    (source (graph core4949) (root 10) 2 2) DegreeTwoThreeSpectrum7354.graph sourceMap4949=true := by decide +kernel
theorem fusedMap4949_checked : acceptsGraphIso
    (fused (graph core4949) (root 10) 2 2) DegreeTwoThreeSpectrum6969.graph fusedMap4949=true := by decide +kernel
theorem certified4949 : Certified (graph core4949) (root 10) 2 2 :=
  of_native_maps core4949 DegreeTwoThreeSpectrum7354.graph DegreeTwoThreeSpectrum6969.graph
    sourceMap4949 fusedMap4949 sourceMap4949_checked fusedMap4949_checked
    DegreeTwoThreeFiniteComparisons.comparison4949
#print axioms sourceMap4949_checked
#print axioms fusedMap4949_checked
#print axioms certified4949
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
