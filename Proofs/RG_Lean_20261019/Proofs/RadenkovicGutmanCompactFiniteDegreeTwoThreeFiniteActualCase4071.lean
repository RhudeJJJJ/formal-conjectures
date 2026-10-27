/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4071 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap4071 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4071 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4071_checked : acceptsGraphIso
    (source (graph core4071) (root 7) 2 2) DegreeTwoThreeSpectrum2135.graph sourceMap4071=true := by decide +kernel
theorem fusedMap4071_checked : acceptsGraphIso
    (fused (graph core4071) (root 7) 2 2) DegreeTwoThreeSpectrum1826.graph fusedMap4071=true := by decide +kernel
theorem certified4071 : Certified (graph core4071) (root 7) 2 2 :=
  of_native_maps core4071 DegreeTwoThreeSpectrum2135.graph DegreeTwoThreeSpectrum1826.graph
    sourceMap4071 fusedMap4071 sourceMap4071_checked fusedMap4071_checked
    DegreeTwoThreeFiniteComparisons.comparison4071
#print axioms sourceMap4071_checked
#print axioms fusedMap4071_checked
#print axioms certified4071
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
