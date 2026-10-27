/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4087 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap4087 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4087 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4087_checked : acceptsGraphIso
    (source (graph core4087) (root 7) 2 2) DegreeTwoThreeSpectrum2290.graph sourceMap4087=true := by decide +kernel
theorem fusedMap4087_checked : acceptsGraphIso
    (fused (graph core4087) (root 7) 2 2) DegreeTwoThreeSpectrum1805.graph fusedMap4087=true := by decide +kernel
theorem certified4087 : Certified (graph core4087) (root 7) 2 2 :=
  of_native_maps core4087 DegreeTwoThreeSpectrum2290.graph DegreeTwoThreeSpectrum1805.graph
    sourceMap4087 fusedMap4087 sourceMap4087_checked fusedMap4087_checked
    DegreeTwoThreeFiniteComparisons.comparison4087
#print axioms sourceMap4087_checked
#print axioms fusedMap4087_checked
#print axioms certified4087
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
