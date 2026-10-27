/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4178 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap4178 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4178 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4178_checked : acceptsGraphIso
    (source (graph core4178) (root 8) 2 2) DegreeTwoThreeSpectrum3825.graph sourceMap4178=true := by decide +kernel
theorem fusedMap4178_checked : acceptsGraphIso
    (fused (graph core4178) (root 8) 2 2) DegreeTwoThreeSpectrum2649.graph fusedMap4178=true := by decide +kernel
theorem certified4178 : Certified (graph core4178) (root 8) 2 2 :=
  of_native_maps core4178 DegreeTwoThreeSpectrum3825.graph DegreeTwoThreeSpectrum2649.graph
    sourceMap4178 fusedMap4178 sourceMap4178_checked fusedMap4178_checked
    DegreeTwoThreeFiniteComparisons.comparison4178
#print axioms sourceMap4178_checked
#print axioms fusedMap4178_checked
#print axioms certified4178
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
