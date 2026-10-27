/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4196 : Family 9 := level9.get ⟨28,by decide⟩
def sourceMap4196 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4196 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4196_checked : acceptsGraphIso
    (source (graph core4196) (root 9) 2 2) DegreeTwoThreeSpectrum4553.graph sourceMap4196=true := by decide +kernel
theorem fusedMap4196_checked : acceptsGraphIso
    (fused (graph core4196) (root 9) 2 2) DegreeTwoThreeSpectrum3875.graph fusedMap4196=true := by decide +kernel
theorem certified4196 : Certified (graph core4196) (root 9) 2 2 :=
  of_native_maps core4196 DegreeTwoThreeSpectrum4553.graph DegreeTwoThreeSpectrum3875.graph
    sourceMap4196 fusedMap4196 sourceMap4196_checked fusedMap4196_checked
    DegreeTwoThreeFiniteComparisons.comparison4196
#print axioms sourceMap4196_checked
#print axioms fusedMap4196_checked
#print axioms certified4196
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
