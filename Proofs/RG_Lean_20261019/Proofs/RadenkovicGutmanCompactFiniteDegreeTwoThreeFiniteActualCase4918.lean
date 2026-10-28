/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4918 : Family 10 := level10.get ⟨1413,by decide⟩
def sourceMap4918 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap4918 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4918_checked : acceptsGraphIso
    (source (graph core4918) (root 10) 2 2) DegreeTwoThreeSpectrum7475.graph sourceMap4918=true := by decide +kernel
theorem fusedMap4918_checked : acceptsGraphIso
    (fused (graph core4918) (root 10) 2 2) DegreeTwoThreeSpectrum6859.graph fusedMap4918=true := by decide +kernel
theorem certified4918 : Certified (graph core4918) (root 10) 2 2 :=
  of_native_maps core4918 DegreeTwoThreeSpectrum7475.graph DegreeTwoThreeSpectrum6859.graph
    sourceMap4918 fusedMap4918 sourceMap4918_checked fusedMap4918_checked
    DegreeTwoThreeFiniteComparisons.comparison4918
#print axioms sourceMap4918_checked
#print axioms fusedMap4918_checked
#print axioms certified4918
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
