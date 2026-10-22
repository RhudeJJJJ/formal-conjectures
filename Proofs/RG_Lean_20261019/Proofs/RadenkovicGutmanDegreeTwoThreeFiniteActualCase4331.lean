/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4331 : Family 9 := level9.get ⟨432,by decide⟩
def sourceMap4331 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4331 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4331_checked : acceptsGraphIso
    (source (graph core4331) (root 9) 2 2) DegreeTwoThreeSpectrum4808.graph sourceMap4331=true := by decide +kernel
theorem fusedMap4331_checked : acceptsGraphIso
    (fused (graph core4331) (root 9) 2 2) DegreeTwoThreeSpectrum4427.graph fusedMap4331=true := by decide +kernel
theorem certified4331 : Certified (graph core4331) (root 9) 2 2 :=
  of_native_maps core4331 DegreeTwoThreeSpectrum4808.graph DegreeTwoThreeSpectrum4427.graph
    sourceMap4331 fusedMap4331 sourceMap4331_checked fusedMap4331_checked
    DegreeTwoThreeFiniteComparisons.comparison4331
#print axioms sourceMap4331_checked
#print axioms fusedMap4331_checked
#print axioms certified4331
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
