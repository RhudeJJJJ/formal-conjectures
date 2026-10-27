/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4078 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap4078 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,7,8,9,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4078 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4078_checked : acceptsGraphIso
    (source (graph core4078) (root 7) 2 2) DegreeTwoThreeSpectrum2180.graph sourceMap4078=true := by decide +kernel
theorem fusedMap4078_checked : acceptsGraphIso
    (fused (graph core4078) (root 7) 2 2) DegreeTwoThreeSpectrum1911.graph fusedMap4078=true := by decide +kernel
theorem certified4078 : Certified (graph core4078) (root 7) 2 2 :=
  of_native_maps core4078 DegreeTwoThreeSpectrum2180.graph DegreeTwoThreeSpectrum1911.graph
    sourceMap4078 fusedMap4078 sourceMap4078_checked fusedMap4078_checked
    DegreeTwoThreeFiniteComparisons.comparison4078
#print axioms sourceMap4078_checked
#print axioms fusedMap4078_checked
#print axioms certified4078
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
