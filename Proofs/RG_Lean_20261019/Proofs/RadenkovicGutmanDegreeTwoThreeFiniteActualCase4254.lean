/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4254 : Family 9 := level9.get ⟨230,by decide⟩
def sourceMap4254 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4254 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4254_checked : acceptsGraphIso
    (source (graph core4254) (root 9) 2 2) DegreeTwoThreeSpectrum4847.graph sourceMap4254=true := by decide +kernel
theorem fusedMap4254_checked : acceptsGraphIso
    (fused (graph core4254) (root 9) 2 2) DegreeTwoThreeSpectrum4022.graph fusedMap4254=true := by decide +kernel
theorem certified4254 : Certified (graph core4254) (root 9) 2 2 :=
  of_native_maps core4254 DegreeTwoThreeSpectrum4847.graph DegreeTwoThreeSpectrum4022.graph
    sourceMap4254 fusedMap4254 sourceMap4254_checked fusedMap4254_checked
    DegreeTwoThreeFiniteComparisons.comparison4254
#print axioms sourceMap4254_checked
#print axioms fusedMap4254_checked
#print axioms certified4254
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
