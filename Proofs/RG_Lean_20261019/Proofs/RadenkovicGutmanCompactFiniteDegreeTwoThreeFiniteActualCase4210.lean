/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4210 : Family 9 := level9.get ⟨87,by decide⟩
def sourceMap4210 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4210 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4210_checked : acceptsGraphIso
    (source (graph core4210) (root 9) 2 2) DegreeTwoThreeSpectrum4531.graph sourceMap4210=true := by decide +kernel
theorem fusedMap4210_checked : acceptsGraphIso
    (fused (graph core4210) (root 9) 2 2) DegreeTwoThreeSpectrum4047.graph fusedMap4210=true := by decide +kernel
theorem certified4210 : Certified (graph core4210) (root 9) 2 2 :=
  of_native_maps core4210 DegreeTwoThreeSpectrum4531.graph DegreeTwoThreeSpectrum4047.graph
    sourceMap4210 fusedMap4210 sourceMap4210_checked fusedMap4210_checked
    DegreeTwoThreeFiniteComparisons.comparison4210
#print axioms sourceMap4210_checked
#print axioms fusedMap4210_checked
#print axioms certified4210
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
