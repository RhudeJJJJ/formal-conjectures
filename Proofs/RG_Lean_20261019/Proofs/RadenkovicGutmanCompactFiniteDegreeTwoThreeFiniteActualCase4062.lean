/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4062 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap4062 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4062 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4062_checked : acceptsGraphIso
    (source (graph core4062) (root 7) 2 2) DegreeTwoThreeSpectrum2168.graph sourceMap4062=true := by decide +kernel
theorem fusedMap4062_checked : acceptsGraphIso
    (fused (graph core4062) (root 7) 2 2) DegreeTwoThreeSpectrum1720.graph fusedMap4062=true := by decide +kernel
theorem certified4062 : Certified (graph core4062) (root 7) 2 2 :=
  of_native_maps core4062 DegreeTwoThreeSpectrum2168.graph DegreeTwoThreeSpectrum1720.graph
    sourceMap4062 fusedMap4062 sourceMap4062_checked fusedMap4062_checked
    DegreeTwoThreeFiniteComparisons.comparison4062
#print axioms sourceMap4062_checked
#print axioms fusedMap4062_checked
#print axioms certified4062
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
