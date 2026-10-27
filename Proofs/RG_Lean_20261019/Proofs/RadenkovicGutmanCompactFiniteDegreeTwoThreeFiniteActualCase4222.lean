/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4222 : Family 9 := level9.get ⟨128,by decide⟩
def sourceMap4222 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,9,10,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4222 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4222_checked : acceptsGraphIso
    (source (graph core4222) (root 9) 2 2) DegreeTwoThreeSpectrum4545.graph sourceMap4222=true := by decide +kernel
theorem fusedMap4222_checked : acceptsGraphIso
    (fused (graph core4222) (root 9) 2 2) DegreeTwoThreeSpectrum4162.graph fusedMap4222=true := by decide +kernel
theorem certified4222 : Certified (graph core4222) (root 9) 2 2 :=
  of_native_maps core4222 DegreeTwoThreeSpectrum4545.graph DegreeTwoThreeSpectrum4162.graph
    sourceMap4222 fusedMap4222 sourceMap4222_checked fusedMap4222_checked
    DegreeTwoThreeFiniteComparisons.comparison4222
#print axioms sourceMap4222_checked
#print axioms fusedMap4222_checked
#print axioms certified4222
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
